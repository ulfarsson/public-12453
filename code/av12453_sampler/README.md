# `av12453_sampler/` — uniform random 12453-avoiding permutations and heatmaps

Date: 3 September 2026.  Companion tooling, not part of the certified computation; the paper's Section 8.1 states the sampling result (Proposition 8.2) and shows the heatmap of `examples/ex_n300_1M` (Figure 2).

Given the tables of the counting algorithm, a permutation of length `n` can
be drawn uniformly at random from `Av_n(12453)` by the recursive method:
every avoider is one maximal path of the state machine of the paper
(Theorem 4.3), and the probability of each next letter is a ratio of
completion counts, which the protected-tail factorization (Section 5) and
the first-coordinate translation (Section 7) express through the stored
kernel table `R_{l,a}(q,s)` and the empty-stack table `G_{(p,q)}`.  One
sample costs about `O(n^4)` double-precision operations.

## Files

| file | role |
|---|---|
| `tables.cpp`, `build_tables.sh` | build the tables `R` and `G` in binary64 by the direct reduced recurrence (`N^7/1008` multiply-adds; 8 s at N=100, 170 s at N=150 on 4 threads), file format `AVR1` |
| `avr_table.hpp`, `avr_table.py` | readers (identical indexing in C++ and Python) |
| `avr_check.cpp`, `check_terms.py`, `check_r.py`, `check_prefix.py`, `validate_tables.sh` | table validation: `G_{(n,0)}` against the known terms, every `R` entry against the exact pure-Python reference, layout cross-checks |
| `sampler.cpp`, `sampler_core.hpp`, `build_sampler.sh` | the sampler; `--check` re-sums all candidate weights at every decision |
| `avoid12453.hpp`, `avoid_check.cpp` | independent O(n^2) avoidance test from the trigger lemma (validated against brute force on all permutations of length <= 10) |
| `unif_test.cpp`, `firstletter_test.py`, `pair_law.py`, `prefix_law.py`, `validate_sampler.sh` | uniformity tests: exact chi-square against all avoiders (n <= 10), exact first-letter, pair and prefix laws at n = 20, 100, 150 |
| `plot_perm.py` | dot plot of a single permutation as a PNG (pure Python), same orientation as the heatmaps; `--tikz` also writes it as a TikZ picture (the paper's `figures/perm_n300_tikz.tex`) |
| `vince-heatmaps.py`, `permpal_heatmap.py` | the PermPAL heatmap script (grayscale, one pixel per cell) and a driver that applies it to a `heatmap.py` count matrix |
| `heatmap.py` | PermPAL-style heatmap: CSV of the position/value count matrix, PNG (pure Python, viridis), SVG; prints mean number of left-to-right minima, mean position of `n`, mean first letter |
| `examples/` | `ex_n50`, `ex_n100` (20,000 samples each), `ex_n150` (5,000 samples) and `ex_n300_1M` (1,000,000 samples of length 300; linear, sqrt and log renderings; see `examples/README_n300_1M.md` for the sample files, kept outside the repository); `perm_n50`, `perm_n100`, `perm_n150`, `perm_n300`: dot plots of one uniform random avoider each (`examples/README_single_perms.md`); `ex_n300_1M_permpal` and `ex_n300_1M_permpal_cuberoot`: the same `n=300` counts rendered by the PermPAL script |
| `README_tables.md`, `README_sampler.md` | detailed documentation and measurements |

## Usage

    sh build_tables.sh                          # -> ./tables
    ./tables --N 100 --threads 4 --out N100.avr # 65 MB; N <= 200 (values must fit in binary64)
    sh build_sampler.sh                         # -> ./sampler ./avoid_check ./unif_test
    ./sampler --table N100.avr --n 100 --count 20000 --seed 1 --threads 4 --out s100.txt
    python3 heatmap.py s100.txt -o examples/ex_n100        # writes .csv .png (.svg with --svg)
    ./avoid_check s100.txt                       # independent avoidance check of every line

The sampler writes one permutation per line (values `1..n`, space
separated) and checks every sample for 12453-avoidance by default
(`--no-avoid` to skip).  Output is byte-identical for any thread count at a
fixed seed (sample `i` uses its own PRNG stream).  Speed on this machine with
4 threads: about 400,000 samples/s at n=50, 40,000/s at n=100, 6,000-8,000/s at
n=150 (the audit measured 0.7-0.85 of the sampler README's figures at
n >= 100 under load).

## Scaled tables for n up to 300 and beyond

Raw counts overflow binary64 from N = 277 (a_277 has 1026 bits).  `tables
--scaled` writes the AVR2 format with entries scaled by 2^{-2w} (w the
grade), which is exact and keeps every entry inside the normal double range
for N <= 500; the sampler applies the matching power-of-two factors.  Scaled
and unscaled tables are bit-identical after unscaling, and the sampler's
output is byte-identical for either table at the same seed.  Details,
including the balanced split products that avoid intermediate underflow, in
`README_scaling.md`.  `--binary FILE` writes samples as little-endian uint16
records (`numpy.fromfile(FILE, dtype='<u2').reshape(-1, n)`); `perms_io.py`
reads both formats.

## Exactness

The weights are binary64 approximations of the exact counts (tables
accurate to about 3e-13 relative at N=150; every decision's candidate
weights re-sum to the stored count within 8e-14).  The output is therefore
uniform up to a total-variation distance of order 1e-11 at n=150, far below
anything a heatmap or a statistic can resolve, but this is not an
exact-arithmetic sampler.  An exact variant would use big-integer tables.

## Validation performed (details in `README_sampler.md` and the audit report)

- Every candidate weight the sampler uses was recovered by bisection and
  compared bit-exactly with the corresponding term of the reduced
  recurrence and of the empty-stack recurrence (175,741 candidates over
  10,818 states), including the endpoint multiplicity, the block-exposure
  rule, the zero-block convention and the joint choice of split rank and
  intermediate control.
- Exact uniformity by chi-square against the brute-force list of all
  avoiders at n = 5..10 (e.g. n = 8: 6.7 million samples over 33,286
  avoiders, p = 0.15 and 0.41 for two seeds; n = 10: 108.7 million
  samples over 2,174,398 avoiders, p = 0.46); every avoider appears.
- Exact first-letter law at n = 100 and 150 (p-values spread over
  0.07-0.90 across seeds), exact (pi_1, pi_2) law, and exact prefix laws
  from an independent implementation of the state machine (n = 20, depth
  4, 73,114 bins, p = 0.44; n = 100, depth 3, p = 0.46).
- Zero 12453-containments in more than 400,000 samples at n = 50..150 by
  two independent avoidance tests.

## What the heatmaps show

Mass concentrates along the anti-diagonal from (position 1, value n) to
(position n, value 1): a uniform 12453-avoider is roughly decreasing, with
a bright cell at the top-left (the first letter is large: mean 92.4 at
n=100, 142.1 at n=150) and at the bottom-right, a broad band above the
anti-diagonal, and an almost empty lower-left triangle (small values early
are rare).  Mean number of left-to-right minima: 25.8 at n=100, 38.7 at
n=150; mean position of the maximum: 23.6 and 31.4.
