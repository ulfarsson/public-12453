# `av12453_n300/` — the computation of |Av_n(12453)| for n <= 300

Date: 2 to 3 September 2026.  This directory is a computation-only
supplement; nothing in it is part of the paper `paper/av12453_polytime.tex`,
whose certified series ends at n = 150 (Proposition 8.1).  The result is
`../data/av12453_terms_0_300.txt` (301 lines `n a_n`, SHA-256
`5c79bf6d8a281afec7374ff1b9029fc5a4dddfd7cc286b5e16a47a03c3dc5a7d`); its
first 151 lines coincide with the certified file `../data/av12453_terms_0_150.txt`.
The narrative report is `../../notes/av12453_300_computation_report.md`.

## What was computed and how

The engine evaluates the proved reduced d=2 recurrence (paper Section 7)
with the proved homogeneous split of `../../notes/av12453_speedup_proofs.tex`,
as the certified single-modulus engine the earlier single-modulus homogeneous-split engine (removed 2026-09-06; in git history) does,
but the split is reorganised into dense matrix products per grade and
evaluation point, with 16-bit primes and 16-bit storage so that every
product and every accumulation is exact in binary64 with no modular
reduction inside the kernel; degree-aware pruning of evaluation points;
OpenMP over evaluation points.  Residues of a_n modulo 77 primes below 2^16
(the largest ones, `harness/primes_u16.txt`) were computed one prime at a
time, and the integers were recovered by the Chinese remainder theorem from
the 71 largest primes, whose product exceeds the exact injection bound
B_300 = sum_m C(300,m)^2 |Av_m(1342)| (1136 bits; the same bound as in the
paper's Proposition 8.1); the 6 remaining primes were withheld and agree
with every reconstructed value.

## Layout

- `engine/av12453_gemm_split_v1.cpp`, `engine/README_v1.md`: the engine
  that produced every residue in `../certificates/av12453_residues_300/`
  (sha256 of the source a617f2dce15d9b7d0452281b0d459d81bd3bdca37492e399673e674c5afa5646).
- `engine/av12453_gemm_split_v2.cpp`, `engine/README_v2.md`: the recommended
  engine for future runs: bit-identical output, parallel empty-stack phase,
  hardened `--truth` handling, `-Wall -Wextra` clean, and a `-DUSE_CBLAS`
  path (correctness-tested against `engine/cblas_stub/`, speed untested).
- `engine/build.sh`, `engine/build_primes.sh`, `engine/RUN_ON_LAPTOP.md`:
  building one binary per prime (the modulus is a compile-time constant),
  on Linux/g++ or macOS/clang, and running the whole pipeline.
- `harness/`: `primes.py` (exact B_N from Bona's series, prime lists and
  the number of primes needed), `run_all.sh` (resumable one-prime-at-a-time
  sweep), `reconstruct.py` (CRT with bound check, CERTIFY of every residue
  file against the certified terms for n <= 150, withheld-prime check),
  `compare_residues.py`, `plan.py`, `bona_bound.py`, `residue_io.py`.
- `pyref/ref.py`: an independent pure-Python (pypy3) implementation of the
  reduced recurrence written from the printed equations only; used to
  cross-check the engine's full kernel tables at N = 40 and 60.

## Reproducing

    # 1. primes and bound
    pypy3 harness/primes.py 300
    # 2. one binary per prime (about 1 s each)
    bash engine/build_primes.sh --primes harness/primes_u16.txt --outdir bin --jobs 8
    # 3. resumable sweep, one prime at a time; about 200 s per prime on 8 cores, 6.5 GB
    bash harness/run_all.sh --bindir bin --primes harness/primes_u16.txt --n 300 --threads 8 --outdir residues --extra-args "--prune"
    # 4. reconstruction (checks the bound, the certified prefix and the withheld primes)
    pypy3 harness/reconstruct.py --residues-dir residues --n 300 --output terms_0_300.txt

The sweep of 77 primes took 4 h 10 min wall clock on the Lima VM of an Apple
Silicon laptop (8-CPU quota); see the report for measurements.

## Verification performed

- Every prime's residues for n <= 150 equal the certified terms modulo that
  prime (77 x 151 checks), and the built-in support, degree and evaluation
  checks passed in every run.
- Full kernel tables at N = 40 and N = 60 are byte-identical to
  the earlier single-modulus homogeneous-split engine (removed 2026-09-06; in git history) built with the same modulus and to `pyref/ref.py`;
  the exact-integer tables of `pyref` reduce mod p to the engine's tables.
- All 201 residues at N = 200 agree between the new engine and
  the earlier single-modulus homogeneous-split engine (removed 2026-09-06; in git history) at p = 65521; the N = 300 residues restrict
  exactly to the N = 200 and N = 150 runs.
- The reconstruction was repeated with an independent CRT script
  (written separately from the harness), giving identical output; the six withheld primes agree.
- Engine v2 reproduces the campaign's p = 65521 residues at N = 300.
