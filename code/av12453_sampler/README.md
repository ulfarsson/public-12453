# `av12453_sampler/` — uniform random 12453-avoiding permutations and heatmaps

Companion tooling for Section 8.1 of the paper: the sampler of Proposition 8.1,
the heatmap of Figure 4 (from the data in `examples/`), and the implementation
that Appendix A describes and whose distance from uniformity it bounds.  It is
not part of the certified computation of Section 8.

## How it works

`tables.cpp` evaluates, in binary64, the reduced kernel table
`R_{l,a}(q,s) = K_l((a,q),(0,s))` by the reduced recurrence `eq:R-recurrence`
(Section 7) and the empty-stack values `G_{(p,q)}` by `eq:G-reduced`
(Appendix A), in increasing reduced grade `w = l+a+q` and in parallel over the
rows of one grade.  Every summand is nonnegative, so nothing cancels; no
evaluation/interpolation scheme is used.  `a_n = G_{(n,0)}`.

The sampler draws a permutation by the recursive method.  Its state is the
sorted array of unread values

    U = [ B0: p values below b_1 ][ B1: q values between b_1 and b_2 ][ I_1 ][ I_2 ] ... [ I_s ]

with the controls `(p,q)` and, for each pending block, the control `(c,t)` at
which it is to be exposed (the frames of an explicit stack; `I_1` is the active
head).  Each letter is chosen with probability proportional to one summand of
the recurrences:

* **empty stack** (total `G_{(p,q)}`): early band `h`, weight
  `G_{(h,p+q-1-h)}`; last band `r` together with the exposure control `(c,t)`
  of the new head, weight `R_{q-1-r,p-c}(r,t) G_{(c,t)}`, or `G_{(p,q-1)}` when
  `r = q-1` and the new head is empty;
* **head of size `l`** at control `(p,q)`, to be exposed at `(c,t)` (total
  `R_{l,p-c}(q,t)`): each endpoint of the head (one if `l = 1`), weight
  `R_{l-1,p-c}(q,t)`; early band `c <= h < p`, weight `R_{l,h-c}(q+p-1-h,t)`;
  last band `0 <= r < q`, weight `R_{l+q-1-r,p-c}(r,t)`; interior letter of
  local rank `2 <= j <= l-1` together with the intermediate control `(c',m)`,
  weight `R_{j-1,p-c'}(q,m) R_{l-j,c'-c}(m,t)`.

The candidates are scanned in a fixed order and the scan stops at the first
one whose running sum exceeds `u`, drawn uniformly in `[0, total)` with `total`
the stored value of the state, so the expensive branches are evaluated only
when they are chosen; a sample costs `O(n^4)` table lookups.  The output is the
permutation itself.  Random numbers come from xoshiro256\*\*, seeded per sample
through splitmix64, so the output depends only on `--seed` and the sample
index: it is byte-identical for every thread count.  Every sample is checked
for 12453-avoidance by `avoid12453.hpp`, an independent `O(n^2)` test from the
trigger lemma (Lemma 2.1) that shares no code with the sampler.

## Files

| file | role |
|---|---|
| `tables.cpp`, `build_tables.sh` | the table builder `./tables` (formats below) and `./avr_check` |
| `avr_table.hpp`, `avr_table.py` | readers for C++ and Python, with identical indexing; `avr_table.py` also gives exact values (`R_exact`, `G_exact`) and ratios of entries of different grade (`g_ratio`, `r_ratio`) |
| `avr_mine.py` | a second Python reader, written from the format description in `tables.cpp` and sharing no code with `avr_table.py`; returns unscaled values |
| `avr_check.cpp`, `avr_cmp.cpp` | a C++ reader for index cross-checks; bit-identity comparison of two tables of any formats |
| `check_terms.py`, `check_r.py`, `check_prefix.py`, `check_ratios.py`, `validate_tables.sh` | table checks: `G_{(n,0)}` against the known terms, every `R` entry against the exact reference `../av12453_n300/pyref/ref.py`, tables of different `N` against each other, scaled against unscaled ratios |
| `sampler.cpp`, `sampler_core.hpp`, `build_sampler.sh` | the sampler `./sampler`, and `./avoid_check`, `./unif_test` |
| `avoid12453.hpp`, `avoid_check.cpp` | the independent avoidance test, and a standalone checker for a file of samples (`--brute` adds a naive containment search) |
| `unif_test.cpp`, `firstletter_test.py`, `pair_law.py`, `prefix_law.py`, `law_test.py`, `validate_sampler.sh` | uniformity tests: chi-square against the list of all avoiders (`n <= 10`), the exact first-letter law, and the exact laws of the first two and the first `m` letters (`law_test.py` compares a law written by `pair_law.py` or `prefix_law.py` with a sample file) |
| `validate_scaling.sh`, `build_all.sh` | the checks of the scaled tables, and the build of every table they need |
| `perms_io.py` | reader and writer for the text and binary sample formats |
| `heatmap.py`, `permpal_heatmap.py`, `vince-heatmaps.py` | the position/value count matrix of a sample file (CSV and PNG), and its PermPAL rendering by the PermPAL script `vince-heatmaps.py` |
| `plot_perm.py` | dot plot of one permutation (PNG, and with `--tikz` a TikZ picture) |
| `bench_speed.sh` | sampling speed with the scaled tables |
| `examples/` | the data behind Figure 4, see `examples/README.md` |

## Building and running

    sh build_tables.sh                                     # -> ./tables ./avr_check
    sh build_sampler.sh                                    # -> ./sampler ./avoid_check ./unif_test
    ./tables --N 100 --threads 4 --out N100.avr            # unscaled table, 65 MB
    ./tables --N 300 --threads 8 --scaled --out N300s.avr  # scaled table, 5.4 GB
    ./sampler --table N100.avr --n 100 --count 20000 --seed 1 --threads 4 --out s100.txt
    ./avoid_check s100.txt                                 # independent check of every line
    python3 heatmap.py s100.txt -o heat_n100               # count matrix (CSV) and PNG

`sampler --table FILE --n N --count M [--seed S] [--threads T] [--out FILE]
[--binary FILE] [--check] [--checktol X] [--no-avoid] [--quiet] [--stats]`
needs a table with `N >= n`.  It writes one permutation per line (values
`1..n`); `--binary FILE` writes little-endian `uint16` records instead or as
well (`numpy.fromfile(FILE, dtype='<u2').reshape(-1, n)`).  `--check` re-sums
all candidate weights at every decision and compares the sum with the stored
value (relative tolerance `--checktol`, default `1e-9`); `--stats` reports the
numbers of decisions, interior splits and rescans.

## Table formats

`AVR1` (unscaled), little-endian:

    int32  magic 0x41565231, int32 N
    double G[p][q]        p = 0..N, q = 0..N-p
    double R[l][a][q][s]  l = 1..N, a = 0..N-l, q = 0..N-l-a, s = 0..slen(a,q)-1

with `slen(a,q) = q+1` for `a = 0` and `a+q` for `a >= 1`, the support of
`R_{l,a}(q,.)` by Lemma 7.1.  `AVR2` (scaled) has the header
`int32 magic 0x41565232, int32 N, int32 scale` (`scale = 2`) and the same
layout, and stores `R'_{l,a}(q,s) = 2^{-2(l+a+q)} R_{l,a}(q,s)` and
`G'_{(p,q)} = 2^{-2(p+q)} G_{(p,q)}`.

The counts grow a little faster than `2^{3.7 n}` (`a_300` has 1115 bits), so
unscaled entries leave the binary64 range from `N = 277` on; `tables` warns
above `N = 200` without `--scaled`.  The scaled entries of the `N = 300` table
lie between `2^{-600}` and `2^{515}`, and the format is good to about
`N = 500`.  Scaling by powers of two is exact: a scaled table multiplied back
is bit-identical to the unscaled one.  In the split products the factor
`4^{m-1}` is applied to one factor, or split evenly between the two when that
factor would overflow, so that no product of two small entries underflows;
both paths give bit-identical results (tested with `--force-balanced`).  The
sampler forms every ratio of entries of different grade with the matching
power of two, so a scaled and an unscaled table give byte-identical samples at
the same seed.

## Exactness

The weights are binary64 approximations of the exact counts, so this is not an
exact-arithmetic sampler.  At each decision `u` is drawn in `[0, total)` with
`total` the stored value, while the scan accumulates the recomputed candidate
weights; the two agree only to about `1e-13` relative.  If `u` lands above the
scanned mass, the sampler multiplies `u` by `mass/total` and scans again, so
every decision ends in a legal move; the result is not exactly proportional to
the evaluated weights (two weights 1 and 1 with stored total 2.1 are chosen
with probabilities 1/2.1 and 1.1/2.1).  Appendix A of the paper bounds all of
these effects together: for the scaled tables with `N = 300` and ideal random
bits, the output is within total-variation distance
`n(g/(1-g) + 7 nu u) < 3.5e-5` of uniform for every `n <= 300`
(Proposition A.2; `nu = 3,352,801`, `u = 2^-53`, `g = gamma_{nu N}`).  The
proved bound is pessimistic: the observed table errors below suggest a
distance of order `1e-11` at `n = 150`, but that figure is an estimate, not a
theorem.  `--stats` counted no rescan in the runs where it was recorded (for
example 100,000 samples at `n = 150`).

## Validation

    sh validate_tables.sh        # unscaled tables N = 40, 60, 100, 150 and the table checks
    sh validate_sampler.sh       # the sampler checks, on those tables
    sh build_all.sh && sh validate_scaling.sh    # scaled tables and their checks

Figures marked (2026-10-01) were rerun on that date with the scripts as they
are now; the others were recorded when the tools were built (September 2026).

**Tables.**
* Every nonzero `R` entry against the exact integers of `../av12453_n300/pyref/ref.py`:
  maximum relative error `1.173e-14` over the 224,680 entries at `N = 40` and
  `4.28e-15` over the 35,425 at `N = 25`, the same for the scaled and the
  unscaled table, and the index sets of nonzero entries coincide (2026-10-01).
* `G_{(n,0)}` against the known terms, in exact rational arithmetic: maximum
  relative error `3.13e-13` for `n <= 150` (2026-10-01), `1.50e-12` for
  `n <= 200`, `4.17e-12` for `n <= 250` and `8.9e-12` for `n <= 300`.
* Scaled and unscaled tables are bit-identical after unscaling at
  `N = 60, 100, 150` (all 42.8 million entries at `N = 150`); tables of
  different `N` agree bit for bit on their common entries; the C++ and Python
  readers agree on 40,000 random probes, and `avr_mine.py` agrees with
  `avr_table.py` on every entry.

**Weights.**  Every candidate weight the sampler uses, recovered by bisection,
equals the corresponding summand of `eq:R-recurrence` or `eq:G-reduced` bit for
bit (175,741 candidates over 10,818 states, covering the endpoint
multiplicity, block exposure, empty blocks and the joint choice of split rank
and intermediate control).  With `--check`, the candidate weights of every
decision re-sum to the stored value within `2.4e-14` relative at `n = 100` and
`7.8e-14` at `n = 150` (45,000 decisions), and exactly for `n <= 20`; with
`--checktol 1e-15` the check fails, as it should.

**Avoidance.**  No sample contained 12453 (more than 400,000 samples at
`n = 50..150`, and all 10^6 at `n = 300`); `avoid12453.hpp` agrees with a naive
search on all permutations of length at most 10.

**Uniformity.**
* Chi-square against the list of all avoiders, with every avoider seen:
  `n = 7` (4,581 avoiders, 916,200 samples, p = 0.26), `n = 8` (33,286
  avoiders, 6.66 million samples, p = 0.15), `n = 9` (260,927 avoiders, 52.2
  million samples, p = 0.52), `n = 10` (2,174,398 avoiders, 108.7 million
  samples, p = 0.46); the scaled tables give p = 0.26 and 0.15 at `n = 7, 8`.
* First letter, `P[pi_1 = k] = G_{(k-1,n-k)}/G_{(n,0)}`: ten runs of 100,000
  samples at `n = 100` and `n = 150`, p-values from 0.07 to 0.90; at
  `n = 100`, 10^6 samples from the scaled `N = 150` table give p = 0.748, mean
  first letter 92.369 against the exact 92.371 (2026-10-01).
* The law of the first two letters and of the first four letters at `n = 20`,
  computed through `avr_mine.py` and, for the prefixes, an independent
  implementation of the scan: p = 0.87 (380 pairs, 200,000 samples) and
  p = 0.45 (112,404 prefixes, 10^6 samples); reversed samples and a sample
  beginning with a prefix of probability zero are rejected (2026-10-01).

The versions of `check_terms.py`, `check_r.py` and `firstletter_test.py`
published before 2026-10-01 compared stored scaled values with unscaled counts
on `AVR2` tables, `check_r.py` returned success whenever the supports agreed,
and `avr_mine.py` was missing; an outside review found these defects, and
the scripts were corrected and the affected figures rerun.

## Measurements

On an 8-core aarch64 machine with g++ 14.2:

| `N` | format | table build, 8 threads | file |
|---|---|---|---|
| 100 | AVR1 or AVR2 | 4.3 s | 65 MB |
| 150 | AVR1 or AVR2 | 104 s | 342 MB |
| 200 | AVR2 | 12 min | 1.08 GB |
| 250 | AVR2 | 56 min | 2.63 GB |
| 300 | AVR2 | 3 h 58 min | 5.4 GB |

The build needs about the size of the table in memory, and its kernel phase
grows like `N^7`.  Sampling speed without the avoidance check, which costs a
further 5–10%:

| `n` | 1 thread | 4 threads | 8 threads |
|---|---|---|---|
| 100 | 13,700/s | 48,300/s | 94,400/s |
| 150 | 2,130/s | 7,580/s | 13,000/s |
| 200 | 610/s | 2,140/s | 2,970/s |
| 250 | 190/s | 750/s | 1,010/s |

(with the avoidance check: about 400,000/s at `n = 50` on 4 threads, and 490/s
at `n = 300` on 8 threads).  The sampler's memory is the table, shared by all
threads.

## What the heatmaps show

Mass concentrates along the anti-diagonal from (position 1, value `n`) to
(position `n`, value 1): a uniform 12453-avoider is roughly decreasing, with a
large first letter (mean 92.37 at `n = 100`, 142.15 at `n = 150`, 291.91 at
`n = 300`), a broad band above the anti-diagonal and an almost empty lower-left
triangle.  The mean number of left-to-right minima is 25.8, 38.7 and 77.5 at
`n = 100, 150, 300`, and the mean position of the maximum 23.7, 31.4 and 53.5.
