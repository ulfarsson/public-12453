# Exact coefficients of `Av(12453)` through length 300

Date: 3 September 2026.  Status: computation only; not part of the paper,
whose certified series ends at n = 150 (Proposition 8.1).  Author decision
(2 September 2026): extend the series with the fast engine, nothing to be
added to the manuscript.

## Result

`code/data/av12453_terms_0_300.txt` holds `a_0, ..., a_300` (301 lines
`n a_n`), SHA-256

```text
5c79bf6d8a281afec7374ff1b9029fc5a4dddfd7cc286b5e16a47a03c3dc5a7d
```

Its first 151 lines coincide with the certified file
`code/data/av12453_terms_0_150.txt`.  The last term has 336 decimal digits:

```text
a_300 = 2393824208816418444965604920369002401672...
```

Consecutive ratios `a_n/a_{n-1}` are 13.7401, 14.0130, 14.1551, 14.2431,
14.3031 at n = 100, 150, 200, 250, 300, approaching the Stanley--Wilf limit
`9 + 4 sqrt 2 = 14.6569` from below.

## Method

The residues of `a_n` modulo the 77 largest primes below 2^16 were computed
one prime at a time by `code/av12453_n300/engine/av12453_gemm_split_v1.cpp`
(source SHA-256 `a617f2dce15d9b7d0452281b0d459d81bd3bdca37492e399673e674c5afa5646`),
and the integers were recovered by the Chinese remainder theorem
(`code/av12453_n300/harness/reconstruct.py`).

The engine evaluates the proved reduced d = 2 recurrence (paper Section 7)
with the proved homogeneous split (`notes/av12453_speedup_proofs.tex`), as
the certified single-modulus engine `code/av12453_homog_split.cpp` does.
Two changes make it fast: (i) for each grade `W` and evaluation point `y_j`,
the split contributions are dense matrix products `A B` where `A` collects
all evaluated slices of one grade and `B` those of one offset grade, so the
inner loop is a blocked GEMM (4 x 8 binary64 FMA micro-kernel, NEON or
portable); (ii) with a 16-bit prime every product is below 2^32 and every
accumulated sum below 2^53, so no modular reduction happens inside the
kernel and all arithmetic is exact in binary64.  Degree-aware pruning uses
only the `W - q - 2` evaluation points a coordinate needs.  Storage is 16-bit
for the evaluated table; the reduced table is kept only for the two most
recent grades plus a copy for the empty-stack phase.

Bound and primes.  With `b_m = |Av_m(1342)|` from Bona's algebraic series,
`B_300 = sum_m C(300,m)^2 b_m` has 1136 bits (B_150 has 558, as in the
paper).  The product of the 71 largest primes below 2^16 has 1136 bits and
exceeds `B_300`; the six next primes (`64703, 64693, 64689, 64679, 64667,
64661`) were withheld from reconstruction and agree with every reconstructed
value.

## Verification

- Every residue file passes CERTIFY: residues for n <= 150 equal the
  certified terms modulo the prime (77 x 151 checks, by the engine and by
  two independent comparators).  Every run also passed the built-in support
  check, degree check (`deg_y Phi_W(.;q,.) <= W-q-3`), evaluation check
  (unused evaluation points reproduce the interpolant) and the binary64
  reduction self-test.
- Full kernel tables at N = 40 and N = 60 are byte-identical to
  `code/av12453_homog_split.cpp` built with the same modulus and to the
  independent pure-Python implementation `code/av12453_n300/pyref/ref.py`
  written from the printed equations; the exact-integer tables of `ref.py`
  reduce modulo p to the engine's tables (224,680 and 1,117,520 entries).
- All 201 residues at N = 200 agree between the new engine and
  `code/av12453_homog_split.cpp` at p = 65521; the N = 300 residues restrict
  exactly to the N = 200 and N = 150 runs.
- The reconstruction was repeated with an independent CRT script; identical
  output, bound exceeded, six withheld primes in agreement, certified prefix
  reproduced exactly.
- Frozen asymptotic fit of the paper (Conjecture 10.2 (numbered 10.1 since 2026-09-13), parameters fixed on
  n <= 100): the maximum of `|log a_n - model|` is 4.3e-7 on 101 <= n <= 150
  (the paper reports below 4.2e-7 from the exact fit parameters) and grows
  smoothly to 3.0e-4 at n = 300 (6.0e-6 at 175, 2.3e-5 at 200, 1.1e-4 at
  250).  The drift is monotone and slow, consistent with the neglected
  `O(n^{-2/3})` correction, and does not contradict the conjectured form;
  it does show that a refit on 300 terms would move the parameters.

## Cost

Machine: Lima VM on an Apple Silicon laptop, aarch64, 8-CPU quota, 16 GiB.
Sweep of 77 primes, 8 threads, one prime at a time: started 20:35 UTC on
2 September, finished 00:45 UTC on 3 September (4 h 10 min); per prime
185 to 215 s, mean 199 s; peak RSS 6.5 GiB.  Split work per prime
1.56e13 structural multiply-adds (1.88e13 issued), 2.2e10 issued
multiply-adds per second per thread.  For comparison, the certified engine
`av12453_homog_split.cpp` at N = 200 on the same machine and prime took
116 s and 2.6 GiB against 25 s and 1.3 GiB for the new engine, and its own
N = 300 estimate was about 2 hours and 12.7 GiB per prime.

Engine v2 (`av12453_gemm_split_v2.cpp`, bit-identical output, parallel
empty-stack phase), measured after the sweep on the idle machine: N = 300,
p = 65521, 8 threads, 150.0 s wall (empty-stack phase 10.4 s instead of
63.5 s), peak RSS 6.5 GiB, residues identical to the campaign file.  A
future sweep of 77 primes with v2 would take about 3.2 hours here.

## Files

- `code/data/av12453_terms_0_300.txt`: the result.
- `code/certificates/av12453_residues_300/`: the 77 residue files and the
  sweep log.
- `code/av12453_n300/`: engines v1 and v2, build and run scripts, harness,
  pure-Python reference, project brief; `README.md` there describes the
  layout and how to reproduce, `engine/RUN_ON_LAPTOP.md` the laptop
  pipeline.
