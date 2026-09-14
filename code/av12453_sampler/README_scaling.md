# Scaled (AVR2) tables and the sampler for `n` up to 300

Working directory `scratch/n300_2026-09-02/scaled/`, a copy of
`repo/code/av12453_sampler/` with the changes described here.  Date: 3
September 2026.  Machine: aarch64, 8 threads, 16 GB.

Nothing here enters the paper: this is companion tooling for uniform random
sampling from `Av_n(12453)` and for the heatmaps.

## 1. Why the tables have to be scaled

`|Av_n(12453)|` grows a little faster than `2^{3.7 n}`: from the certified
terms, `log2(a_n)/n` rises from 3.510 at `n = 100` through 3.655 at `n = 200`
to 3.717 at `n = 300` (`a_300` has 1115 bits).  The kernel entries
`R_{l,a}(q,s)` at grade `w = l+a+q` reach the same size.  So an unscaled
`AVR1` table overflows binary64 (`2^1024`) at `N = 277`, where `a_n` first
needs 1026 bits.

The fix is to store every entry divided by an exact power of two that depends
only on its grade:

| stored | definition | grade |
|---|---|---|
| `R'_{l,a}(q,s)` | `2^{-2w} R_{l,a}(q,s)` | `w = l+a+q` |
| `G'_{(p,q)}`    | `2^{-2m} G_{(p,q)}`    | `m = p+q`   |

The measured ranges (section 7) are `R' in [2^{-2w}, 2^{1.72 w}]` and
`G' in [2^{-4}, 2^{1.72 m}]`, so at `N = 300` every stored entry lies between
`2^{-600}` and `2^{516}`, comfortably inside the normal binary64 range
(`[2^{-1022}, 2^{1024}]`); the format is good to about `N = 500`.

Because the scale factor is a power of two, the scaling is **exact**: no
mantissa bit is lost.  If the same operations are performed in the same order
and nothing over- or underflows, the scaled table multiplied back by
`2^{2w}` is *bit-identical* to the unscaled table.  Check (1) below verifies
exactly that, on every one of the 42.8 million entries at `N = 150`.

## 2. The recurrence in the scaled variables

With `w = l+a+q` the grade of the row being computed:

```
early band :  2^{-2} R'_{l,h}(a+q-h-1, s)              (source grade w-1)
last band  :  2^{-2} R'_{l+q-r-1,a}(r, s)              (source grade w-1)
D term     :  l = 1 :  2^{-2w} [a = 0 and q = s]
              l >= 2:  2^{-2} * 2 R'_{l-1,a}(q,s)
split      :  sum 4^{m-1} R'_{l1,a1}(q,m) R'_{l2,a2}(m,s)
              because w1 + w2 = (l1+a1+q) + (l2+a2+m) = w - 1 + m
```

and for `G'`, with `m = p+q` the mass:

```
early band :          2^{-2} G'_{(h, m-1-h)}
zero block (r = q-1): 2^{-2} G'_{(p, q-1)}
last band  :          4^{t-1} R'_{l,p-c}(r,t) G'_{(c,t)},  l = q-1-r >= 1
G'_{(0,0)} = 1
```

### The balanced products

The split factor `4^{m-1}` must **not** be applied as `(R' R') * 4^{m-1}`.
Both factors can be as small as `2^{-2N}`; at `N = 300` their product would be
`2^{-1200}`, which underflows to zero.  That would silently delete the split
contribution of exactly the entries that are smallest and most likely to be
`1` in exact arithmetic (for instance `R_{l,0}(q,q) = C_l`, the Catalan
number, whose scaled value at `q = 299` is about `2^{-600}`).

The factor is therefore always split evenly between the two factors,
`(2^{m-1} R') * (2^{m-1} R')`.  Two code paths implement it (`tables.cpp`,
`computeRow`):

* **fast path.** `vv = R'_{l1,a1}(q,m) * 4^{m-1}` is formed once per `m` for a
  whole `A` row into a scratch buffer, and the inner loop over `s` stays the
  plain axpy `row[s] += vv * B[s]` of the unscaled build.  This is exact and
  cannot lose the product, because the *result* `2^{-2w} R1 R2` is always in
  range; the only risk is `vv` itself overflowing.
* **balanced path**, used for the (rare) `m` where `vv` would overflow: the
  `B` row is pre-multiplied by `2^{m-1}` into a scratch buffer and the `A`
  entry by `2^{m-1}`, and the same axpy is run on the pre-multiplied row.

Both give bit-identical results (the power-of-two factors are exact, and the
mantissa product and its accumulation are the same in both).  The build
reports how many inner loops took each path; at `N <= 250` the balanced path
is never needed (0 of 5.7e10 loops at `N = 200`), but it is what makes the
scheme safe at `N = 300` and beyond.

The same balancing is applied in the `G` last band (`4^{t-1} R' G'`): the
`2^{t-1}` of the `G` factor is folded into a permanently maintained side array
`GS[(c,t)] = G'_{(c,t)} * 2^{t-1}`, and the `2^{t-1}` of the `R` factor into a
per-row scratch buffer, so that the dot product has exactly the same shape as
the unscaled one.

### One subtlety: keep the loop *shape* identical, not just the values

The first version of the scaled `G` phase wrote the dot product as
`acc += (rr[v] * pw) * gs[v]` instead of pre-scaling `rr` into a buffer.  The
values are the same, but g++ contracts `acc += x*y` into a fused multiply-add
(`-ffp-contract=fast` is the default) and it made a different contraction
decision for the two shapes, which changed 10 of the 861 `G` entries at
`N = 40` by one ulp.  Nothing was wrong with the scaling -- compiling with
`-ffp-contract=off` made both builds agree again -- but pre-scaling into a
buffer restores bit-identity *and* keeps the FMA.  This is worth remembering:
"same value" is not enough for bit-identity; the expression tree handed to the
compiler has to be the same too.

## 3. File format AVR2

```
int32  magic = 0x41565232        ('A','V','R','2')
int32  N
int32  scale                     (exponent per grade unit; 2)
double G[...]                    p = 0..N, q = 0..N-p        (as in AVR1)
double R[...]                    l = 1..N, a = 0..N-l, q = 0..N-l-a,
                                 s = 0..slen(a,q)-1          (as in AVR1)
```

The header is 12 bytes instead of AVR1's 8; the two data blocks have exactly
the AVR1 layout.  `AVR1` is unchanged and is still what `./tables` writes
without `--scaled`.

Both readers accept both formats and expose the scale:

* `avr_table.hpp` -- `Table::scale` (0 for AVR1), `Table::scaled()`,
  `Table::R()/G()` return the value **as stored**, `Table::R_true()/G_true()`
  apply `ldexp` by `scale*grade`.
* `avr_table.py` -- `AvrTable.scale`, `.hdr`, `.R()/.G()` (stored),
  `.R_true()/.G_true()` (unscaled: a float when representable, an exact
  Python `int` beyond `2^1024`), `.R_exact()/.G_exact()` (`Fraction`, always
  exact), and `.g_ratio()/.r_ratio()` for ratios of entries of different
  grade, which is what the distribution tests need.
  `python3 avr_table.py FILE --info` prints the format and scale;
  `--terms A:B --true` prints the unscaled `a_n` as exact integers.

## 4. The sampler with a scaled table

Within one decision the candidate weights come from several different grades,
so they must all be divided by the grade factor of the decision's own total
before they are compared.  At a block state `(l, (p,q), (c,t))` of grade
`w = l + (p-c) + q`:

| move | scaled weight |
|---|---|
| endpoint (each of the 1 or 2) | `2^{-2} R'_{l-1,p-c}(q,t)` |
| `l = 1` block exposure | `2^{-2w} [ (p,q) = (c,t) ]` |
| early band `h` | `2^{-2} R'_{l,h-c}(q+p-1-h, t)` |
| last band `r` | `2^{-2} R'_{l+q-1-r,p-c}(r, t)` |
| split `(j, c', m)` | `4^{m-1} R'_{a,p-c'}(q,m) R'_{b,c'-c}(m,t)`, balanced |

and at the top level, control `(p,q)` of mass `m`:

| move | scaled weight |
|---|---|
| early band `h` | `2^{-2} G'_{(h, q+p-1-h)}` |
| zero block | `2^{-2} G'_{(p,r)}` |
| last band `(r,c,t)` | `4^{t-1} R'_{l,p-c}(r,t) G'_{(c,t)}`, balanced |

These sum to the stored `R'_{l,p-c}(q,t)` resp. `G'_{(p,q)}`, which is what
`--check` compares against (tolerance `--checktol`, default 1e-9).

Because every scale factor is an exact power of two, each weight, each partial
sum and the threshold `u = rng.u01() * total` are all exactly `2^{-2w}` times
their unscaled counterparts, so every comparison in the walk goes the same
way: **the scaled and the unscaled sampler produce byte-identical output from
the same seed** (check (3)).  The scaled sampler is not an approximation of
the unscaled one; it is the same walk with a different exponent bookkeeping.

`sampler_core.hpp` implements this by templating the two candidate scans on
`bool SCALED`, dispatched once per sample, so the unscaled code path is
untouched.

## 5. `--binary` output and `perms_io.py`

`sampler --binary FILE` writes the samples, in sample order, as a flat stream
of little-endian `uint16` values, `n` per record, with no header and no
separators; values are `1..n`.  That is `2n` bytes per sample instead of about
`4n` for the text form (at `n = 300`: 600 bytes vs 1136).  With numpy:

```python
a = np.fromfile(FILE, dtype='<u2').reshape(-1, n)     # values 1..n
```

`--out` and `--binary` may be given together and then hold the same samples;
with only `--binary` no text is written; with neither, the text goes to
stdout.

`perms_io.py` is the pure-Python (numpy-free, pypy3-friendly) reader:

```python
from perms_io import iter_perms
for pi in iter_perms("s300.bin", n=300):   # or iter_perms("s300.txt")
    ...
```

plus `iter_text`, `iter_binary`, `count_records` (O(1) on the binary form),
`write_text`, `write_binary`, `check_perms`, and a format sniffer
`looks_binary`.  CLI: `--count`, `--head K`, `--validate`, `--to-text OUT`,
`--to-binary OUT`, `--compare OTHER`.

## 6. Files changed

| file | change |
|---|---|
| `tables.cpp` | `--scaled` writes AVR2; the recurrence is templated on `bool SCALED`; balanced split products; range audit of the finished table |
| `avr_table.hpp` | reads AVR1 and AVR2; `scale`, `scaled()`, `R_true()`, `G_true()` |
| `avr_table.py` | ditto, plus `R_exact/G_exact` (Fraction), `g_ratio/r_ratio`, `terms_true`, `--true` |
| `sampler_core.hpp` | candidate scans templated on `bool SCALED` with the weights of section 4 |
| `sampler.cpp` | `--binary FILE` |
| `avr_cmp.cpp` | **new**: bit-identity comparison of two AVR tables (any mix of formats) |
| `perms_io.py` | **new**: pure-Python reader/writer for both sample formats |
| `heatmap.py` | reads the `--binary` sample format too (auto-detected; needs `-n`) |
| `check_terms.py` | compares in exact rational arithmetic, so it works past `n = 260` |
| `check_r.py`, `check_prefix.py`, `firstletter_test.py` | scale-aware |
| `build_all.sh`, `validate_scaling.sh` | **new**: build and validation drivers |

`avoid12453.hpp`, `avoid_check.cpp` and `unif_test.cpp` are unchanged
(`unif_test` picks the scaled path up through `sampler_core.hpp`).
`pair_law.py` and `prefix_law.py` are unchanged and still need the audit's
independent reader `avr_mine.py`; they support AVR1 only.

## 7. Validation

Everything below was run on this machine (aarch64, 8 threads, 16 GB, g++
14.2.0, `-O3 -mcpu=native -funroll-loops -fopenmp`), with

```
sh build_all.sh              # tables; add 250 for the N = 250 table
sh validate_scaling.sh       # checks (1)-(6); full log in logs/validate_scaling.log
```

### (1) Scaled vs unscaled tables are bit-identical

`avr_cmp` multiplies every stored entry of both tables by `2^{scale*grade}`
and compares the two binary64 values **bit by bit**.

```
$ ./avr_cmp N60u.avr  N60s.avr    R  1,117,520 entries, 0 mismatches;  G  1,891 entries, 0 mismatches
$ ./avr_cmp N100u.avr N100s.avr   R  8,504,200 entries, 0 mismatches;  G  5,151 entries, 0 mismatches
$ ./avr_cmp N150u.avr N150s.avr   R 42,759,425 entries, 0 mismatches;  G 11,476 entries, 0 mismatches
```

`verdict PASS (bit-identical)` in all three cases; no entry was skipped for
overflow, and no entry was zero in one table and nonzero in the other.  The
same tool also confirms `N`-independence across formats (a bonus check):
`N40s` vs `N60u`, `N60s` vs `N100u`, `N100s` vs `N150s` and `N40u` vs `N150s`
all agree bit for bit on their common support.

A stronger version of the same check: the *unmodified* `tables.cpp` of
`repo/code/av12453_sampler/` was compiled separately and run at `N = 100`, and
its table is bit-identical both to the AVR1 table of this directory and (after
rescaling) to the AVR2 one:

```
$ g++ -std=c++17 -O3 -mcpu=native -funroll-loops -fopenmp \
      -o /tmp/origtbl/tables_orig /tmp/origtbl/tables.cpp   # repo copy, untouched
$ /tmp/origtbl/tables_orig --N 100 --threads 4 --out /tmp/origtbl/N100_orig.avr
$ ./avr_cmp /tmp/origtbl/N100_orig.avr N100u.avr   -> PASS (bit-identical)
$ ./avr_cmp /tmp/origtbl/N100_orig.avr N100s.avr   -> PASS (bit-identical)
```

So neither the templating of the recurrence nor the scaling changed a single
bit of the arithmetic the repository already produced.

Two further checks of the same tables:

* against the exact pure-Python reference `pyref/ref.py` at `N = 40`
  (224,680 nonzero entries, exact integers): the scaled table gives exactly
  the same maximum relative error as the unscaled one,
  `1.179566e-14 at R(14,21,3,0)`, and **the index sets of nonzero entries
  coincide** -- nothing underflowed to zero:

  ```
  $ pypy3 code/av12453_n300/pyref/ref.py 40 --dump-r dump40.txt
  $ pypy3 check_r.py N40s.avr dump40.txt      # identical output to check_r.py N40u.avr
  entries compared 224680 / stored entries 224680
  max relative err 1.179566e-14  at (l,a,q,s)=(14, 21, 3, 0)
  nonzero in dump but 0.0 in table: 0
  index sets of nonzero entries coincide: YES
  ```

* the C++ and Python readers agree on the scaled format:
  `./avr_check N40s.avr --probe 987654321 20000` and
  `pypy3 avr_table.py N40s.avr --probe 987654321 20000` produce
  byte-identical 40,000-line probe listings.

* `pypy3 check_ratios.py N150s.avr N150u.avr --n 150` compares the exact
  first-letter law and 4,000 random kernel ratios computed through
  `g_ratio`/`r_ratio` from the scaled and the unscaled table: maximum relative
  difference `0.000e+00` in both, i.e. the grade factors cancel exactly.
  `firstletter_test.py` with the scaled `N150s.avr` at `n = 100`, 40,000
  samples: chi-square 23.28 on 38 dof, p = 0.971, empirical mean first letter
  92.377 against the exact 92.371.

* the balanced fallback path, which the fast path makes unnecessary below
  `N ~ 280`, was exercised deliberately with `--force-balanced` (which sets
  the fast-path threshold to 0):

  ```
  $ ./tables --N 100 --threads 8 --scaled --force-balanced --out N100b.avr
  split inner loops: 0 fast (v*4^{m-1}), 2697180255 balanced (100%)
  $ ./avr_cmp N100s.avr N100b.avr   -> PASS (bit-identical)
  $ ./avr_cmp N100u.avr N100b.avr   -> PASS (bit-identical)
  ```

  so both split paths are verified, and the one that will actually be used at
  `N = 300` is not an untested branch.  Forcing it everywhere costs 22% of the
  kernel phase (5.19 s vs 4.03 s at `N = 100`).

### (2) `G'_(n,0) * 2^{2n}` against the known terms

`check_terms.py` now compares in exact rational arithmetic
(`AvrTable.G_exact` multiplies the stored double by the exact power of two),
so the check keeps working past `n = 260` where `a_n` no longer fits in
binary64.

| table | terms compared | max relative error | at | verdict (tol 1e-11) |
|---|---|---|---|---|
| `N150s.avr` | `n = 0..150` | `3.130576e-13` | `n = 150` | PASS |
| `N200s.avr` | `n = 0..200` | `1.499098e-12` | `n = 200` | PASS |
| `N250s.avr` | `n = 0..250` | `4.169674e-12` | `n = 250` | PASS |

The error grows like `n^2 * 2^-53` as expected from `O(n^2)` rounded additions
per entry; the unscaled `N150u.avr` gives *exactly* the same `3.130576e-13`
(the two tables are bit-identical).  `a_200` has 731 bits and `a_250` 923
bits, so both are still inside binary64 (`a_n` first passes `2^1024` at
`n = 277`).  The point of the scaling at these `N` is therefore not the answer
but the *split products*: the unbalanced form `(R' R') * 4^{m-1}` is already
losing bits at `N = 256`.  At `N = 300` the entries themselves no longer fit
either.

### (3) Sampler: scaled table vs unscaled table

```
$ ./sampler --table N150u.avr --n 150 --count 10000 --seed 20260903 --threads 4 --out u150.txt
$ ./sampler --table N150s.avr --n 150 --count 10000 --seed 20260903 --threads 4 --out s150.txt
PASS: byte-identical at n = 150 (4,920,000 bytes)
PASS: byte-identical at n = 100 (2,920,000 bytes)
```

and the weight-sum assertions with the scaled table:

```
$ ./sampler --table N150s.avr --n 150 --count 200 --seed 20260903 --threads 1 --check --stats
weight-sum check: PASS (worst relative deviation 7.462e-14, tol 1.0e-09)
decisions=30000 (150.00/sample) interior=3044 (15.220/sample) rounding-rescans=0
```

The worst deviation is `7.462e-14` with the scaled table and `7.462e-14` with
the unscaled table -- the same number to every digit, as it must be, since
each scaled weight is exactly `2^{-2w}` times the unscaled one.

### (4) Avoidance and exact uniformity from the scaled tables

Every sample drawn in this validation passed the independent trigger-lemma
avoidance test built into the sampler, and the sample files were re-checked
with the standalone `avoid_check` (which for `n <= 12` also runs the
brute-force containment search):

| n | table | samples | 12453-containments |
|---|---|---|---|
| 7 | `N40s.avr` | 100,000 | 0 (brute force agrees on all) |
| 8 | `N40s.avr` | 100,000 | 0 (brute force agrees on all) |
| 12 | `N40s.avr` | 100,000 | 0 (brute force agrees on all) |
| 100 | `N150s.avr` | 50,000 | 0 |
| 150 | `N150s.avr` | 20,000 | 0 |

Exact chi-square against the brute-force list of all avoiders, scaled
`N40s.avr`, seed 20260903:

```
n = 7:  4,581 avoiders, 916,200 samples, every avoider seen,
        chi-square 4641.09, dof 4580, X2/dof 1.0133, p = 0.2603   PASS
n = 8: 33,286 avoiders, 6,657,200 samples, every avoider seen,
        chi-square 33557.93, dof 33285, X2/dof 1.0082, p = 0.1451  PASS
```

(the Wilson-Hilferty normal approximation agrees to six digits in both cases,
and the trigger-lemma test agrees with brute force on all 5,040 resp. 40,320
permutations).

### (5) `--binary` output

```
$ ./sampler --table N150s.avr --n 150 --count 1000 --seed 20260903 --threads 4 \
            --out b150.txt --binary b150.bin
b150.bin  300,000 bytes   (= 1000 * 150 * 2)
b150.txt  492,000 bytes
$ pypy3 perms_io.py b150.bin --n 150 --count            -> 1000
$ pypy3 perms_io.py b150.txt --compare b150.bin --n 150 -> 0 of 1000 differ, PASS
$ pypy3 perms_io.py b150.bin --n 150 --validate         -> 1000 records, all permutations of 1..150
$ pypy3 perms_io.py b150.bin --n 150 --to-text b150r.txt; cmp b150.txt b150r.txt -> identical
```

and the binary stream is the same whether or not `--out` is also given.

### (6) Speed with the scaled tables

`--no-avoid` (raw sampling), samples/s and the derived cost per sample per
thread; the avoidance check costs a further 5-10% at these lengths.

| n | table | 1 thread | 4 threads | 8 threads | ms/sample/thread (1 thr) |
|---|---|---|---|---|---|
| 100 | `N150s.avr` | 13,667/s | 48,270/s | 94,358/s | 0.073 |
| 150 | `N150s.avr` | 2,132/s | 7,575/s | 12,986/s | 0.469 |
| 200 | `N200s.avr` | 608/s | 2,141/s | 2,970/s | 1.646 |
| 250 | `N250s.avr` | 188/s | 751/s | 1,006/s | 5.316 |

With the avoidance check on: 6,278/s at `n = 150`, 2,026/s at `n = 200` and
722/s at `n = 250` (4 threads).

The per-sample cost grows like `n^{4.4}`-`n^{5.3}` here, the exponent rising
with `n` (the asymptotic count is `O(n^4)` table lookups per sample; the extra
exponent is cache and TLB pressure -- the table is 342 MB at `N = 150`,
1.04 GB at `N = 200` and 2.63 GB at `N = 250`).  Parallel efficiency falls off
for the same reason: 8 threads give 7.0x at `n = 100`, 4.9x at `n = 200` and
5.3x at `n = 250`.

Sampler peak RSS is the table size itself (1,031 MiB at `N = 200`): the table
is loaded once and shared by all threads.

### Table build times and ranges (8 threads)

| N | format | kernel phase | total | peak RSS | file | `R'` range | balanced splits |
|---|---|---|---|---|---|---|---|
| 100 | AVR1 | 4.27 s | 4.31 s | 68 MiB | 65 MB | `[1, 2^349.6]` | - |
| 100 | AVR2 | 4.03 s | 4.08 s | 68 MiB | 65 MB | `[2^-200, 2^149.6]` | 0 of 2.70e9 |
| 150 | AVR1 | 104.4 s | 104.9 s | 329 MiB | 342 MB | `[1, 2^539.4]` | - |
| 150 | AVR2 | 103.0 s | 103.5 s | 329 MiB | 342 MB | `[2^-300, 2^239.4]` | 0 of 3.10e10 |
| 200 | AVR2 | 718.6 s | 720.8 s | 1031 MiB | 1.08 GB | `[2^-400, 2^330.3]` | 0 of 1.75e11 |
| 250 | AVR2 | 3331.6 s | 3337.9 s | 2508 MiB | 2.63 GB | `[2^-500, 2^421.7]` | 0 of 6.70e11 |

The scaled build costs **the same** as the unscaled one (within noise): the
`4^{m-1}` factor is folded into the `A` row once per `m`, so the inner loop
over `s` is byte for byte the same axpy as in the unscaled build.

The measured extremes match the theory exactly.  The smallest nonzero `R'` is
`2^{-2N}` on the nose (attained by the entries equal to 1 at the top grade),
and the largest stored `G'` is `G'_{(N,0)} = 2^{-2N} a_N`, so the growth rate
of the counts can be read straight off the audit line:
`log2(a_200) = 400 + 330.9 = 730.9 = 3.655 * 200`, and `log2(a_300)/300 =
3.717` from the certified terms.  The stored entries therefore lie in
`[2^{-2w}, 2^{1.72 w}]`.

At `N = 300` that puts every stored entry in `[2^{-600}, 2^{516}]`, and the
balanced split factors `2^{m-1} R'` in `[2^{-601}, 2^{815}]` -- all far inside
the normal binary64 range `[2^{-1022}, 2^{1024}]`, and inside the
`[2^{-2N-1}, 2^{2.8N}]` window the brief asked to confirm.

For contrast, the *unbalanced* product `R' * R'` of two minimal entries would
be `2^{-4N}`: subnormal for `N >= 256` and an exact zero for `N >= 269`.  That
is the failure the balanced form prevents, and it would be silent -- the
affected entries are exactly the small ones such as `R_{l,0}(q,q) = C_l`.
The *fast* form `R' * 4^{m-1} <= 2^{3.72 w1 - 2}` overflows when
`3.72 w1 > 1026`, i.e. from about `N = 277`, which is why the `N = 300` build needs the balanced
fallback and why it was tested with `--force-balanced`.

## 8. Building the `N = 300` table and drawing 10^6 samples of length 300

```sh
cd code/av12453_sampler
sh build_tables.sh                                   # -> ./tables ./avr_check
sh build_sampler.sh                                  # -> ./sampler ./avoid_check ./unif_test
g++ -std=c++17 -O2 -Wall -Wextra -o avr_cmp avr_cmp.cpp

# the table: about 3.5 h on 8 threads, 5.4 GB resident, 5.4 GB on disk
nohup ./tables --N 300 --threads 8 --scaled --verbose --out N300s.avr \
      > logs/build_N300s.log 2>&1 &

# sanity checks once it is written
./avr_cmp N250s.avr N300s.avr                        # bit-identical on the common support
pypy3 check_terms.py N300s.avr --tol 1e-11           # G'_(n,0)*2^{2n} vs the known terms, n <= 300
pypy3 avr_table.py N300s.avr --info                  # format, scale, a_300 as an exact integer

# 10^6 uniform samples of length 300, text and binary, 8 threads
./sampler --table N300s.avr --n 300 --count 1000000 --seed 1 --threads 8 \
          --out s300.txt --binary s300.bin --stats

# spot checks on the output
./avoid_check s300.txt                               # independent avoidance test, every line
pypy3 perms_io.py s300.txt --compare s300.bin --n 300
pypy3 perms_io.py s300.bin --n 300 --validate
./sampler --table N300s.avr --n 300 --count 50 --seed 1 --threads 1 --check --out /dev/null
python3 heatmap.py s300.txt -o examples/ex_n300
```

Expected resources:

* **table build**: kernel phase scales as `N^7`; measured 720.8 s at `N = 200`
  and 3,331.6 s at `N = 250` on 8 threads (ratio 4.62 vs the predicted 4.77),
  so `N = 300` is `(300/250)^7 = 3.58` times the `N = 250` build, about
  **3.3 h**.  Memory: `R` needs `N^4/12` doubles = 5.4 GB, plus a 5.4 GB
  write; peak RSS about **5.5 GB**.  Some of the split inner loops will take
  the balanced path (see section 7); that costs at most 22% if it happened
  everywhere, and far less in practice.
* **10^6 samples at n = 300**: measured 5.32 ms per sample per thread at
  `n = 250` on one thread and 7.96 ms on eight, growing like `n^{5.25}`, so
  `n = 300` costs about 14 ms on one thread and 21 ms per thread on eight,
  i.e. roughly **390 samples/s, 45 min for 10^6 samples on 8 threads**
  (allow 35-70 min).  Output: 1.14 GB of text (`s300.txt`) and 600 MB of binary
  (`s300.bin`); the sampler streams both in blocks of 4096 samples, so its
  own memory stays at the table size, about **5.5 GB**.  Add `--no-avoid` to
  skip the per-sample avoidance test (5-10% faster) once it has been seen to
  pass on a smaller run.

The table build and the sampling run cannot be done at the same time on this
machine: together they need 11 GB and both saturate the memory bandwidth.

## 9. Exactness statement (unchanged in substance)

The weights are binary64 approximations of exact integer counts.  With the
scaled tables the *relative* accuracy is exactly what it was before -- the
scaling is a change of exponent only -- so the table error is about `3e-13`
at `N = 150` and `1.5e-12` at `N = 200`, growing like `n^2 * 2^-53`, and the
output is uniform up to a total-variation distance of that order times the
number of decisions.  That is far below what a heatmap or a sample statistic
can resolve, but this is not an exact-arithmetic sampler; an exact variant
would need big-integer tables.
