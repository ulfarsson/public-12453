# Independent pure-Python reference for the reduced d = 2 recurrence

Directory: `code/av12453_n300/pyref/`
Date: 2026-09-02.  Interpreter: PyPy 7.3.23 (Python 3.11.15), aarch64, 9 CPUs,
single-threaded throughout.

## 1. What was written, and from what

`ref.py` (single file, ~470 lines) implements the reduced `d = 2` recurrence
directly from the printed equations of
`paper/av12453_polytime.tex`:

* `eq:support-d2` (Lemma "Exact two-threshold support"),
* `eq:d2-translation` (Lemma "First-coordinate translation") and
  `eq:R-definition`, `R_{l,a}(q,s) = K_l((a,q),(0,s))`,
* `eq:R-recurrence` with its `D` term and the support statement,
* `eq:G` (Corollary "Empty-stack recurrence", Section "Protected tails and
  transfer kernels") together with `eq:T`, `eq:U` and `eq:answer-G`,
* `eq:d2-second-translation` (used only as an extra check, not in the
  recurrence itself).

No repository code was read or reused.  The only repository files opened were
the manuscript `paper/av12453_polytime.tex` and the certified data file
`code/data/av12453_terms_0_150.txt`
(sha256 `f5ab4017ec65a661d8fbcd84d2f7893afe5e2c695dd082ace58399f7960340fc`).
In particular the earlier homogeneous-split engine, its README, and the
speedup notes were **not** opened.

### Equations as implemented

Row lengths follow the exact support of `eq:support-d2` transported through the
first-coordinate translation: `supp R_{l,a}(q,.) = {0..q}` for `a = 0` and
`{0..a+q-1}` for `a >= 1`, i.e.

```
scount(a,q) = q+1   if a == 0,      a+q   if a >= 1.
```

Kernel phase (`eq:R-recurrence`, evaluated literally, memoized in increasing
reduced grade `w = l+a+q`, for `w = 1..MG`):

```
R_{l,a}(q,s) = sum_{h=0}^{a-1} R_{l,h}(a+q-h-1, s)              early band
             + sum_{r=0}^{q-1} R_{l+q-r-1,a}(r, s)              last band
             + D_{l,a}(q,s)
             + sum_{l1+l2=l-1, l1,l2>=1} sum_{a1+a2=a} sum_{m>=0}
                   R_{l1,a1}(q,m) * R_{l2,a2}(m,s)              split
D_{1,a}(q,s) = [a = 0 and q = s],   D_{l,a}(q,s) = 2 R_{l-1,a}(q,s)  (l >= 2).
```

The split is the **direct triple sum** over `(l1, a1, m)` -- no homogeneity
slices, no evaluation at points, no interpolation.  Every band/D source has
grade `w-1`; every split factor has grade `<= w-2`, so the per-grade schedule
is well founded (this was checked at run time by the fact that every source
row read was already materialised).

Empty-stack phase.  For `d = 2`, `eq:T` gives `T_{0,h}((p,q)) = (h, p+q-1-h)`
and `eq:U` gives `U_h((p,q)) = (p,h)`, `delta_h = q-1-h`.  Applying
`eq:d2-translation` to the kernel factor of `eq:G`,
`K_delta((p,h),(u,v)) = R_{delta, p-u}(h,v)` for `0 <= u <= p` (and `0`
otherwise, by the support lemma), while `delta = 0` contributes the identity
kernel:

```
G_(p,q) = [p = q = 0]
        + sum_{h=0}^{p-1} G_(h, p+q-1-h)
        + sum_{h=0}^{q-2} sum_{a=0}^{p} sum_{v < scount(a,h)}
              R_{q-1-h, a}(h, v) * G_(p-a, v)
        + [q >= 1] G_(p, q-1)                      (the h = q-1, delta = 0 term)
a_n = G_(n,0).
```

Controls are processed in increasing mass `m = p+q`; every term on the right
has mass `<= m-1`.  Grades `<= N-1` of the R table suffice for terms up to
`n = N`; `ref.py` computes grades `1..N` by default so that the dumps are
defined up to grade `N`.

Arithmetic.  Exact Python integers by default; with `--mod P` every stored row
is reduced to `[0,P)`.  Inside the split, products are accumulated without
reduction while the running total is provably below `2^62` (the code reduces
the row whenever the number of accumulated products would exceed
`2^62 / (P-1)^2`), which keeps PyPy on its machine-word integer path.

## 2. CLI and file formats

```
ref.py N [--mod P] [--dump-r FILE] [--terms FILE]
         [--max-grade G] [--dump-all] [--support-check M] [--support-pad K]
         [--brute B] [--trans-check] [--check-data [FILE]] [--progress]
         [--stats FILE]
```

Exit status is nonzero if any requested check fails.

**`--dump-r FILE` format (exact specification, for cross-engine comparison).**
One line per entry:

```
l a q s value\n
```

* fields separated by a single ASCII space, no leading/trailing spaces, LF line
  endings, no header line, no trailing blank line;
* `l >= 1`, `a >= 0`, `q >= 0`, `l+a+q <= G` where `G = --max-grade` (default
  `N`); `0 <= s < scount(a,q)`, i.e. only terminal coordinates **inside** the
  stated support appear;
* lines are in ascending lexicographic order of the integer 4-tuple
  `(l, a, q, s)` (i.e. sorted by `l`, then `a`, then `q`, then `s`);
* `value` is the residue in `[0,P)` when `--mod P` is given, otherwise the
  exact nonnegative integer;
* **by default entries whose value is 0 are omitted** (the task's "all nonzero
  entries within the support").  Over the integers no in-support entry is ever
  zero (the support lemma is an equality of sets, and this was verified for
  every row of grade `<= 60`), but a value can vanish modulo `P`: 11 of the
  1,117,520 entries vanish mod 65521 at `N = 60`, none mod 2097143.  For
  engines that emit zeros, `--dump-all` produces the same file with those
  lines present (`*_all.txt` below), and `compare_dump.py` treats a missing key
  as the value 0 so either convention compares equal.

**`--terms FILE` format**: one line `n a_n` per `n = 0..N`, ascending, single
space, LF.  Residue in `[0,P)` under `--mod P`.

`compare_dump.py A B [--mod P] [--max-grade G]` compares two dumps in this
format by key, tolerating the zero-line convention and allowing a smaller
grade window; exit status 0 iff they agree.

## 3. Checks run (all PASS)

| check | how | result |
|---|---|---|
| exact `a_n`, `n <= 60`, vs data file | `ref.py 60 --check-data` (exact integers) | **PASS**, 61/61 terms equal `av12453_terms_0_150.txt` |
| exact `a_n`, `n <= 40` | `ref.py 40 --check-data` | **PASS**, 41/41 |
| residues `n <= 100` mod 2097143 | `ref.py 100 --mod 2097143 --check-data` | **PASS**, 101/101 terms equal the data file mod P |
| residues `n <= 60` mod 65521 and mod 2097143 | `--check-data` in every dump run | **PASS**, 61/61 each |
| support statement, exact, all rows of grade `<= 60` | `ref.py 60 --support-check 60 --support-pad 3` | **PASS**: 37,820 rows recomputed with 3 extra terminal coordinates each; 0 nonzero entries outside the stated support; and 0 zero entries inside it (the lemma is an equality, so both halves hold over Z) |
| support statement, mod 65521 / mod 2097143, grade `<= 60` | `--support-check 60` | **PASS**: 0 outside-support nonzeros; 11 (resp. 0) in-support entries vanish mod P, which is allowed |
| support statement, exact, grade `<= 40` | `ref.py 40 --support-check 40` | **PASS**: 11,480 rows, 0/0 |
| brute force `n <= 8` | `ref.py 8 --brute 8`; own containment test (all `C(n,5)` position subsets, standardisation of the selected values, comparison with the pattern `(1,2,4,5,3)` of `12453`) | **PASS**: `1, 1, 2, 6, 24, 119, 694, 4581, 33286` equals the recurrence and the data file |
| containment test itself | `test_brute.py`: the same brute force applied to other patterns | **PASS**: `Av(231)` = Catalan `1,1,2,5,14,42,132`; `Av(1342)` = `1,1,2,6,23,103,512,2740` (Bona, A022558); `Av(12345)` = `1,1,2,6,24,119,694,4582` equals an independent RSK/hook-length computation, and differs from `Av(12453)` at `n = 7` (4582 vs 4581), so the test really tests the pattern `12453` |
| second-coordinate translation `eq:d2-second-translation` | `ref.py 60 --trans-check` (exact) | **PASS**, 557,845 instances of `R_{l,a}(q+1,s+1) = R_{l,a}(q,s)` for `s >= a-1` |
| paper's printed values | `dump_N40_exact.txt` | `R_{1,2}(1,1) = 3` and `R_{1,2}(0,0) = 2`, as printed after the lemma |
| mod path vs exact path, whole R table at `N = 40` | `cmpdump.py dump_N40_exact.txt dump_N40_p*.txt P` | **PASS**: all 224,680 entries agree after reduction, for both primes |
| truncation independence | `compare_dump.py dump_N40_p65521.txt dump_N60_p65521.txt --max-grade 40` | **PASS**: the `N = 40` dump is exactly the grade `<= 40` part of the `N = 60` dump |
| stored-entry count vs the paper | counted at run time | `N(N+1)(N^2+N+4)/12` of `eq:d2-first-reduced-counts` reproduced exactly: 224,680 (`N=40`), 1,117,520 (`N=60`), 8,504,200 (`N=100`) |

Zero-modulo-P entries are listed in `zero_entries_N40_p65521.txt` (4 entries)
and `zero_entries_N60_p65521.txt` (11 entries), in the dump format.

## 4. Dumps delivered (for the C++ cross-check)

| file | N (= max grade) | prime | lines | sha256 |
|---|---|---|---|---|
| `dump_N40_p65521.txt` | 40 | 65521 | 224,676 | `a2622a062ed7468dd21ea5932b41fcb8543e93b09891cc651327ac3c37ecc608` |
| `dump_N40_p65521_all.txt` | 40 | 65521 | 224,680 (zeros kept) | `6f29016e38d0737a95df0f0d338477eb94fc5fceb241edb5d8659419ef4bfbb8` |
| `dump_N40_p2097143.txt` | 40 | 2097143 | 224,680 | `53d428b30221bc2ace3b184f91a3536cc6fca8485aaddfa7349f8e9818b88e05` |
| `dump_N60_p65521.txt` | 60 | 65521 | 1,117,509 | `3f6efe808d4301f792491e237cbeee9c2c0095f8dd7a7a5235e2ac5d76ed5341` |
| `dump_N60_p65521_all.txt` | 60 | 65521 | 1,117,520 (zeros kept) | `a46ecc654f88468d9fa01d4e06b9c1159efd52fd0e03efa7abaa4f53182c66b1` |
| `dump_N60_p2097143.txt` | 60 | 2097143 | 1,117,520 | `3429b709a88a16334ecf303e3bf08c26a8428ebc36a7b042adc3114edd19dff6` |
| `dump_N40_exact.txt` | 40 | none (exact) | 224,680 | `7c5670fb5e129ff08cc77b8e476e7dc517cb73ca377a19459254e039343840a5` |
| `dump_N60_exact.txt` | 60 | none (exact) | 1,117,520 | `20174633ec4d90ff6c9504af9f753430200c8a91a59c3d06926a190bb85a42e2` |

(`dump_N40_p2097143_all.txt` is byte-identical to `dump_N40_p2097143.txt`, and
so is the `N = 60` pair, since no entry vanishes mod 2097143.)

All checksums are in `SHA256SUMS.txt`.

Terms files: `terms_N40_exact.txt`, `terms_N60_exact.txt`,
`terms_N{40,60}_p{65521,2097143}.txt`, `terms_N100_p2097143.txt`.

## 5. Timings and counts (single thread, PyPy)

| run | N | arithmetic | split multiply-adds | kernel s | empty-stack s | total s | peak RSS |
|---|---|---|---|---|---|---|---|
| `ref.py 40` | 40 | exact | 137,899,112 | 3.08 | 0.06 | 3.21 | 114.9 MiB |
| `ref.py 40 --mod 65521` | 40 | mod | 137,899,058 | 0.79 | 0.01 | 0.83 | 107.0 MiB |
| `ref.py 40 --mod 2097143` | 40 | mod | 137,899,112 | 0.78 | 0.01 | 0.82 | 107.5 MiB |
| `ref.py 60` | 60 | exact | 2,482,811,568 | 74–82 | 0.6–1.1 | 74.6 (clean) / 83.9 (with a second job on the box) | 307.5 MiB |
| `ref.py 60 --mod 65521` | 60 | mod | 2,482,794,704 | 13.41 | 0.04 | 13.59 | 126.2 MiB |
| `ref.py 60 --mod 2097143` | 60 | mod | 2,482,811,568 | 13.37 | 0.04 | 13.55 | 124.5 MiB |
| `ref.py 100 --mod 2097143` | 100 | mod | 92,651,749,953 | 583.3 | 0.77 | 584.1 | 192.7 MiB |
| `ref.py 60 --support-check 60` | 60 | exact | 2 x 2,482,811,568 | 75.4 + 86.2 | | 162.2 | 336.9 MiB |

Throughput: **1.58–1.85e8 multiply-adds/s** modulo a prime (`u21` and `u16`
primes are indistinguishable), **3.0–4.5e7/s** over the exact integers (a_60
has 200 bits, so the exact split multiplies 3–4 limb integers).  The
empty-stack phase is negligible (166,749,990 multiply-adds at `N = 100`,
0.77 s).

The executed multiply-add count agrees with the closed form
(`madd_count.py`, verified against a brute enumeration of the loop nest for
`N <= 100`)

```
count(N) = sum_{l+a+q<=N, l>=3} (l-2) * sum_{a1+a2=a} sum_{m<scount(a1,q)} scount(a2,m)
```

exactly in exact arithmetic; modulo `P` it is smaller by the products skipped
when a first factor vanishes (54 at `N = 40`, 16,864 at `N = 60`, mod 65521).

```
N        40         60         100        150         200         300
madds  1.379e8    2.483e9    9.265e10   1.619e12    1.227e13    2.120e14
```

Extrapolation of this literal reference (1.6e8 madd/s, single thread):
`N = 150` ~ 2.8 h, `N = 200` ~ 21 h, `N = 300` ~ 15 days per prime; storage
`N(N+1)(N^2+N+4)/12` entries = 42.8M (`N=150`), 134.7M (`N=200`), 679.5M
(`N=300`), i.e. roughly 0.6 GiB, 1.8 GiB and 8.5 GiB in PyPy's unboxed integer
lists.  The literal reference is therefore usable as a cross-check up to about
`N = 100–150` and is not a route to `N = 300`; that is the point of the
evaluation/interpolation engine.

For the record, the retained-entry count of the second translation,
`N(N+1)(N^2+N+10)/24`, evaluates to 339,791,375 at `N = 300`, matching the
figure quoted in `BRIEF.md`.

## 6. Notes for the cross-engine comparison

1. Compare with `compare_dump.py` (or any tool that treats an absent key as
   zero).  If the C++ `--dump-r` emits zero-valued in-support entries, compare
   against the `*_all.txt` files, or just use `compare_dump.py`, which handles
   both.
2. The dump covers `l+a+q <= G` with `G = N`.  If the other engine dumps only
   grades `<= N-1` (grades `<= N-1` are all that the terms need), restrict with
   `--max-grade N-1` on both sides.
3. Index convention: `l >= 1` is the block size, `a >= 0` the reduced first
   control coordinate (`a = p - c` of `eq:d2-translation`), `q >= 0` the second
   source coordinate, `s` the second terminal coordinate; the value is
   `R_{l,a}(q,s) = K_l((a,q),(0,s))`.  Rows are **not** compressed by the
   second-coordinate translation: every in-support `s` is present.
4. Sanity anchors independent of any implementation: `R_{1,0}(0,0) = 1`,
   `R_{1,0}(2,0) = 3`, `R_{1,1}(1,0) = 2`, `R_{1,2}(0,0) = 2`,
   `R_{1,2}(1,1) = 3` (the last two are printed in the paper), and
   `R_{2,0}(0,0) = 2`.

## 7. Files

* `ref.py` -- the reference implementation (the deliverable).
* `compare_dump.py` -- dump comparison tool for the cross-engine check.
* `madd_count.py` -- closed-form a-priori multiply-add count; `count.py` -- the
  naive loop-nest count it was validated against.
* `test_brute.py` -- validation of the brute-force containment test.
* `cmpdump.py` -- exact-vs-modular dump comparison used in section 3.
* `dump_*.txt`, `terms_*.txt`, `zero_entries_*.txt`, `SHA256SUMS.txt` -- outputs.
* `run_*.log`, `stats_*.json` -- raw run logs and machine-readable sidecars.
* `bench.py` -- the PyPy inner-loop microbenchmark used to size the runs.

## 8. What was not done

* No `N = 150/200/300` runs from this reference: the literal `O(N^7)` split
  makes them 2.8 h / 21 h / 15 days per prime single-threaded (see the table);
  the brief's 40-minute budget rules them out.  The largest run performed is
  `N = 100` mod 2097143 (584 s), which certifies 101 terms against the data
  file.
* No comparison against `av12453_homog_split.cpp` was performed here: reading
  or building repository code was outside this task's scope ("do not read or
  reuse any repo code except the data file").  The dumps above are the input to
  that comparison.
* The exact-integer mode was run to `N = 60` (the task's requirement) and not
  beyond; `N = 100` exact would take roughly 1.5–2 h and several GiB.
