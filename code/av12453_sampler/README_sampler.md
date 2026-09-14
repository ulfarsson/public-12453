# `sampler/` — uniform random sampling from `Av_n(12453)`

Date 2026-09-03.  Implements the recursive-method sampler of
`SAMPLER_BRIEF.md`, section "The sampler", on top of the AVR1 double-precision
`R`/`G` tables in `../tables/`.  Repo used read-only; nothing here enters the
paper.

Directory: `code/av12453_sampler/`

| file | role |
|---|---|
| `sampler_core.hpp` | the sampler: state, frame stack, candidate scans, moves, xoshiro256\*\* PRNG |
| `sampler.cpp` | CLI (`sampler`), OpenMP over independent samples |
| `avoid12453.hpp` | **independent** avoidance test (trigger lemma + O(m) 231 test) and a naive O(n^5) containment search |
| `avoid_check.cpp` | standalone checker (`avoid_check`) for a file of permutations |
| `unif_test.cpp` | brute-force enumeration + chi-square uniformity test at small `n` |
| `firstletter_test.py` | first-letter chi-square against `G_{(k-1,n-k)}/G_{(n,0)}` (pypy3, uses `../tables/avr_table.py`) |
| `build.sh` | builds `sampler`, `avoid_check`, `unif_test` |
| `validate.sh` | runs the whole mandatory validation suite |
| `VALIDATION.log`, `VALIDATION_bonus.log`, `VALIDATION_seeds.log` | the recorded output of those runs |

## Build

```sh
sh build.sh          # g++ -std=c++17 -O3 -march=native -funroll-loops -fopenmp
```
`build.sh` auto-detects `-march`/`-mcpu`/no-OpenMP and adds `-I../tables` so
that `avr_table.hpp` is found.  Built and tested with g++ 14.2.0 on aarch64.

## Usage

```
sampler --table FILE --n N --count M [--seed S] [--threads T]
        [--out FILE] [--check] [--checktol X] [--no-avoid] [--quiet] [--stats]
```

* `--table` an AVR1 file from `../tables/` with `N >= n` (`N40/N60/N100/N150.avr`).
* `--out` file to write, default stdout.  One permutation per line, values
  `1..n`, space separated, **in sample order**.
* `--seed` run seed (default 1).  Sample number `i` uses the PRNG stream
  `splitmix64(seed, i)`, so the output is bit-identical for any `--threads`.
* `--threads` OpenMP threads over independent samples (default 1).
* `--check` debug mode: at *every* decision, re-enumerate all candidates and
  assert that their weights sum to the stored count (`G_{(p,q)}` at top level,
  `R_{l,p-c}(q,t)` inside a block) within `1e-9` relative.  Costs ~7x.
  `--checktol X` sets the tolerance (and implies `--check`); a violation
  aborts that sample, is reported, and makes the program exit 1.
* `--no-avoid` skip the per-sample avoidance verification (on by default).
* `--stats` print decision / interior-split / rounding-rescan counts.

Examples:

```sh
./sampler --table ../tables/N100.avr --n 100 --count 20000 --seed 7 \
          --threads 4 --out samples_n100.txt
./sampler --table ../tables/N150.avr --n 150 --count 100 --check --out /dev/null
./avoid_check --brute samples_n12.txt        # standalone independent check
```

The output format is exactly what a heatmap tool wants: `M[i][pi_i]` is
accumulated by reading the file line by line.

## What the sampler does

State (paper Section 4, `eq:H`): the unread values in increasing order are

```
U = [ B0 : p values below b_1 ][ B1 : q values in (b_1,b_2) ][ I_1 ][ I_2 ] ... [ I_s ]
```

so the whole configuration is one sorted array `U` together with `(p,q)` and
the block sizes; `I_1` (the head) is the only readable block.  Each block also
carries the *target control* `(c,t)` at which it must be exposed — those are
the frames of the explicit stack, `frames.back()` being the head.  Deferred
blocks are never touched until they become the head, which is exactly the
"explicit frame stack for deferred blocks" the brief asks for (no recursion:
`sample()` is one flat loop).

Decisions (weights in `double`, from the tables):

* **top level** (empty stack, total `G_{(p,q)}`): early band `h` with weight
  `G_{(h,q+p-1-h)}`; or last band `r` together with the exposure control
  `(c,t)` with weight `R_{q-1-r,p-c}(r,t) G_{(c,t)}` (for `r = q-1` the block
  is empty, `K_0` is the identity, and the weight is `G_{(p,q-1)}`).
* **block** (head of size `l`, control `(p,q)`, target `(c,t)`, total
  `R_{l,p-c}(q,t)`): the two endpoints of `I_1` (one if `l = 1`) with weight
  `R_{l-1,p-c}(q,t)`; early band `c <= h < p` with weight
  `R_{l,h-c}(q+p-1-h,t)`; last band `0 <= r < q` with weight
  `R_{l+q-1-r,p-c}(r,t)`; interior rank `2 <= j <= l-1` with intermediate
  control `(c',m)` and weight `R_{j-1,p-c'}(q,m) R_{l-j,c'-c}(m,t)`.

Concrete unread sets are maintained alongside the counts, so each decision
yields an actual letter (`U[h]`, `U[p+r]`, `U[p+q]`, `U[p+q+l-1]`,
`U[p+q+j-1]`) and the output is the permutation itself.

Candidates are scanned in a fixed order and the scan stops at the first
candidate whose running sum exceeds `u`, so the expensive branches
(top-level last band, `O(q p (p+q))`; interior split, `O(l (p-c+1)(p-c+q))`)
are only paid when they are actually selected.  Worst case per letter is
`O(N^3)`; measured cost is ~10 interior splits per sample at `n = 100` and
~15 at `n = 150`.

## Exactness

With **exact** weights the product of the conditional probabilities along a
complete path telescopes to `1/G_{(n,0)}`, so every element of `Av_n(12453)`
is produced with probability exactly `1/|Av_n(12453)|`.

The tables are `binary64`, so the weights carry a relative error.  Two things
are worth stating precisely.

1. **No guard-band bias.**  At each decision `u` is drawn uniformly in
   `[0, total)` with `total` the *stored* count, and the walk uses the
   *recomputed* candidate weights.  Those two agree only to ~1e-13 relative,
   so `u` can (with probability ~1e-13) exceed the mass the walk actually
   accumulates; in that case the sampler rescales `u` by the accumulated mass
   and walks again.  The realised distribution is therefore *exactly*
   proportional to the evaluated double weights, with no arbitrary guard band.
   (`--stats` reports the number of such rescans; it was 0 in every run
   recorded here, including 100 000 samples at `n = 150`.)
2. **Residual error.**  The remaining deviation from uniformity is the
   tables' own error.  `../tables/REPORT.md` measures `G(n,0)` to
   3.1e-13 relative at `N = 150` (1.3e-14 at `N = 100`), and every stored `R`
   entry to 1.2e-14 at `N = 40` against exact integers.  `--check` measures
   the same thing end-to-end: the largest observed discrepancy between the
   recomputed candidate sum and the stored count was **2.4e-14** relative over
   10 000 decisions at `n = 100` and **7.8e-14** over 45 000 decisions at
   `n = 150` (0 exactly for `n <= 20`, where the counts are small integers).
   Each conditional probability is therefore correct to ~1e-13 relative, and a
   path probability at `n = 150` to ~1e-11 relative.  The total variation
   distance from the exact uniform distribution is of that order — utterly
   negligible for heatmaps and for any statistic estimated from fewer than
   ~1e20 samples.

**This is not an exact-arithmetic sampler.**  It is uniform to ~1e-11 in total
variation at `n = 150`.  Nothing here is used in the paper.

## PRNG

xoshiro256\*\* (Blackman–Vigna), 256-bit state, seeded through splitmix64 with
8 warm-up outputs.  Doubles come from the top 53 bits.  Sample `i` of a run
uses the stream `splitmix64(seed * C1 + C2 * (i+1))`, i.e. one independent
counter-based stream per sample, so results depend on `--seed` and the sample
index only — never on the thread count or the scheduling.  Verified: the
`--threads 1` and `--threads 4` outputs of 3000 samples at `n = 100` are
byte-identical (`validate.sh` step 0).  The first draw of 10^6 distinct
streams is uniform on 1000 bins (chi-square 1005–1040 on 999 dof over four
seeds), so there is no stratification artefact in the per-sample seeding.

## Independent avoidance checker

`avoid12453.hpp` shares no code with the sampler.  It uses the trigger lemma:
`pi` contains `12453` iff some **2-trigger** `c` (a letter with a smaller
letter before it) is followed by three larger letters forming `231`.  The
`231`-containment of a word is decided in linear time by keeping the stack of
right-to-left maxima of the processed prefix: a letter leaves that stack
exactly when a larger letter appears after it, so the word contains `231` iff
some letter is smaller than the largest already-evicted letter.  Total `O(n^2)`
per permutation.  It runs on **every** sample the CLI produces unless
`--no-avoid` is given.

Its own correctness was checked against a completely naive `O(n^5)`
subsequence search on **all** `n!` permutations for `n = 5,6,7,8,9,10`
(`unif_test` step 1: **0 disagreements** out of
120 + 720 + 5 040 + 40 320 + 362 880 + 3 628 800 = 4 037 880 permutations),
and the avoider counts it produces — 119, 694, 4581, 33286, 260927,
2174398 — agree exactly with `repo/code/data/av12453_terms_0_300.txt`.

## Validation results

All commands were run in this directory; full transcripts are in
`VALIDATION.log` (`sh validate.sh`), `VALIDATION_bonus.log` and
`VALIDATION_seeds.log`.  Machine: aarch64, 9 cores, g++ 14.2.0, **4 threads**
as instructed; peak RSS 332 MiB (essentially the 326 MiB `N150.avr` table).

### (0) Determinism

`--threads 1` and `--threads 4`, 3000 samples at `n = 100`, seed 20260903:
byte-identical output. **PASS**

### (1) Avoidance — every generated sample avoids 12453

| n | samples | table | in-sampler check | standalone `avoid_check` | distinct sampled |
|---|---|---|---|---|---|
| 7 | 200 000 | N40 | 0 violations | 0 contain (brute force agrees) | 4581 = all of `Av_7` |
| 8 | 200 000 | N40 | 0 violations | 0 contain (brute force agrees) | 33 207 / 33 286 (expected 33 204) |
| 12 | 200 000 | N40 | 0 violations | 0 contain (brute force agrees) | 199 885 |
| 50 | 200 000 | N60 | 0 violations | 0 contain | 200 000 |
| 100 | 100 000 | N100 | 0 violations | 0 contain | 100 000 |
| 150 | 100 000 | N150 | 0 violations | 0 contain | 100 000 |

Plus 108.7 million samples at `n = 10` and 52.2 million at `n = 9` inside
`unif_test`, every one of them checked: 0 violations.  **PASS**

### (2) Exact uniformity at n = 7 and n = 8 (chi-square vs the brute-force list)

```
./unif_test --table ../tables/N40.avr --n 7 --seed 20260903 --threads 4
./unif_test --table ../tables/N40.avr --n 8 --seed 20260903 --threads 4
```

| n | avoiders | samples | avg/class | every avoider seen | min/max count | chi-square | dof | X²/dof | p |
|---|---|---|---|---|---|---|---|---|---|
| 7 | 4 581 | 916 200 | 200 | **YES** | 143 / 266 | 4641.09 | 4580 | 1.01334 | **0.2603** |
| 8 | 33 286 | 6 657 200 | 200 | **YES** | 149 / 264 | 33557.93 | 33285 | 1.00820 | **0.1451** |

p-values from a self-contained regularized incomplete gamma; the
Wilson–Hilferty normal approximation agrees to 6 digits. **PASS**

Bonus (`VALIDATION_bonus.log`; same test, whole recursion including interior
splits, which occur 0.033 / 0.073 / 0.127 / 0.193 / 0.268 times per sample at
`n = 6,7,8,9,10` — so the frame stack and the split branch really are
exercised by these tests):

| n | avoiders | samples | avg/class | every avoider seen | chi-square | dof | X²/dof | p |
|---|---|---|---|---|---|---|---|---|
| 5 | 119 | 23 800 | 200 | YES | 137.25 | 118 | 1.16314 | 0.1087 |
| 6 | 694 | 138 800 | 200 | YES | 670.28 | 693 | 0.96722 | 0.7255 |
| 9 | 260 927 | 52 185 400 | 200 | YES | 260896.51 | 260926 | 0.999887 | 0.5159 |
| 10 | 2 174 398 | 108 719 900 | 50 | YES | 2174606.68 | 2174397 | 1.000096 | 0.4598 |

### (3) First letter at n = 100 and n = 150, 100 000 samples

`P[pi_1 = k] = G_{(k-1,n-k)}/G_{(n,0)}`; neighbouring `k` merged so that every
expected count is >= 5.

```
./sampler --table ../tables/N100.avr --n 100 --count 100000 --seed S --threads 4 --out f.txt
pypy3 firstletter_test.py --table ../tables/N100.avr --n 100 --in f.txt
```

| n | seed | bins | chi-square | dof | X²/dof | p |
|---|---|---|---|---|---|---|
| 100 | 20260903 | 42 | 43.708 | 41 | 1.066 | 0.357 |
| 100 | 1 / 2 / 3 / 4 | 42 | 39.64 / 38.56 / 39.92 / 55.24 | 41 | | 0.531 / 0.580 / 0.519 / 0.068 |
| 150 | 20260903 | 44 | 31.527 | 43 | 0.733 | 0.902 |
| 150 | 1 / 2 / 3 / 4 | 44 | 48.01 / 56.13 / 35.40 / 46.25 | 43 | | 0.277 / 0.086 / 0.788 / 0.339 |

Means (seed 20260903, 100 000 samples):

| n | mean `pi_1` empirical | mean `pi_1` exact | mean LR minima | mean position of `n` |
|---|---|---|---|---|
| 100 | 92.37100 | 92.37132 | 25.847 | 23.695 |
| 150 | 142.14845 | 142.14850 | 38.705 | 31.365 |

**PASS** (10 independent runs, p-values spread over 0.07–0.90 as they should).

### (4) `--check` weight-sum assertions

| run | decisions | worst relative deviation (tol 1e-9) |
|---|---|---|
| `--n 100 --count 100` | 10 000 | 2.354e-14 |
| `--n 150 --count 100` | 15 000 | 7.462e-14 |
| `--n 150 --count 300` | 45 000 | 7.787e-14 |
| `--n 12 --count 20000` | 240 000 | 0.000e+00 |
| `--n 6..20 --count 200000` each | up to 4 000 000 | 0.000e+00 |

**PASS** — every decision's candidate weights sum to the stored count, at
top level and inside blocks, at every depth of the frame stack.

*Negative control (the assertion is live, not vacuous):*

```
./sampler --table ../tables/N150.avr --n 150 --count 20 --seed 20260903 --checktol 1e-15
  weight-sum check: FAIL (worst relative deviation 2.077e-14, tol 1.0e-15)
  ERROR: ... weight-sum mismatch (blk): sum=3.7432283853787995e+156
         stored=3.7432283853787218e+156 rel=2.08e-14 at p=131 q=5 depth=1
  exit status 1
```

### (5) Speed (samples per second, 20 000 samples per measurement)

Default = with the mandatory per-sample avoidance check; `--no-avoid` = raw
sampling.

| n | 1 thread | 1 thread `--no-avoid` | 4 threads | 4 threads `--no-avoid` | speed-up (4T) |
|---|---|---|---|---|---|
| 50 | 107 059 | 142 143 | 396 203 | 504 377 | 3.70x |
| 100 | 13 581 | 13 884 | 44 448 | 48 549 | 3.27x |
| 150 | 2 237 | 2 273 | 8 163 | 8 324 | 3.65x |

(Run-to-run variation is 5–10%: another workflow shares this machine.  A
repeat of the same measurements gave 107 916 / 13 106 / 2 302 on one thread
and 389 382 / 49 809 / 7 900 on four.)

Larger production runs (4 threads, output written to a file): 200 000 samples
at `n = 50` in **1.16 s** (173 000/s), 100 000 at `n = 100` in **2.69 s**
(37 200/s including file writing), 100 000 at `n = 150` in **13.4 s**
(7 450/s).  `--check` costs about 7–10x (1447 samples/s at `n = 100`,
192/s at `n = 150`, single thread).

Table load time: 0.04 s (`N100.avr`, 65 MiB), 0.17–0.35 s (`N150.avr`,
326 MiB).  Table *build* time is reported in `../tables/REPORT.md`
(8.0 s for `N = 100`, 168 s for `N = 150`, 4 threads).

The brief's target — tens of thousands of samples at `n = 100` within minutes
on 8 cores — is met with a wide margin: 100 000 samples at `n = 100` take
2.7 s on 4 threads.

## Limits and caveats

* `--n` must not exceed the table's `N`.  The tables must not be built beyond
  `N = 200` in binary64 (see `../tables/REPORT.md`).
* Memory is dominated by the table (326 MiB at `N = 150`), shared by all
  threads; per-thread state is a few kB.  Output is buffered 4096 samples at
  a time to keep memory flat and the order deterministic.
* The `--check` weight-sum assertion uses a 1e-9 relative tolerance as the
  brief specifies; the observed deviations are 4–5 orders of magnitude
  smaller, so a much tighter tolerance would also pass at `N <= 150`.
* Sampling is uniform up to ~1e-11 total variation at `n = 150`, not exactly
  uniform; see "Exactness" above.
