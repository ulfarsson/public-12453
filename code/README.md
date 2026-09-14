# Companion code

This directory contains the reproducibility package for the paper
`paper/av12453_polytime.tex`.  The authoritative coefficient file is
`data/av12453_terms_0_150.txt`; its SHA-256 digest is

```text
f5ab4017ec65a661d8fbcd84d2f7893afe5e2c695dd082ace58399f7960340fc
```

## Fast checks

Run the reference recurrence and its built-in brute-force checks:

```sh
pypy3 av_ir231_poly.py 1 8 --verify-small 8
pypy3 av_ir231_poly.py 2 8 --verify-small 8
pypy3 av12453_reduced.py 10 --verify
```

Reconstruct the certified 151-term sequence from the saved residue files:

```sh
python3 reconstruct_av12453_rns.py \
  certificates/av12453_residues_150_pack0.txt \
  certificates/av12453_residues_150_pack1.txt \
  certificates/av12453_residues_150_pack2.txt \
  --primary-count 18 \
  --independent-residue \
    2305843009213693951:certificates/av12453_residue_150_mersenne.txt \
  --known-prefix data/av12453_terms_0_100.txt \
  --output /tmp/av12453_reconstructed_terms.txt
```

The expected final line is

```text
reconstructed=151 primary=18 redundant=6 independent=1 bound_bits=558 product_bits=558
```

The Python reference checks have no third-party dependencies.  The production
C++ programs require a C++20 compiler; the packed program additionally needs
OpenMP and AVX-512F/AVX-512DQ.  A full `N=150` residue pack took about 28
minutes and roughly 684 MB for its residue table on the machine described in
`../notes/av12453_150_computation_report.md`.  The commands above are quick
checks and do not recompute those packs.

The paper's frozen asymptotic fit and its `n=101..150` holdout are reproduced
with standard-library Python:

```sh
python3 av12453_asymptotic_holdout.py data/av12453_terms_0_150.txt
```

## Extension to n = 300 (faster implementation)

`data/av12453_terms_0_300.txt` (SHA-256
`5c79bf6d8a281afec7374ff1b9029fc5a4dddfd7cc286b5e16a47a03c3dc5a7d`) holds
`a_0,...,a_300`.  It was produced by the GEMM-structured engine and harness in
`av12453_n300/` (see its README), with the residues modulo 77 primes below
2^16 in `certificates/av12453_residues_300/`.  The paper's certified series
remains `data/av12453_terms_0_150.txt`; the two files agree on `n <= 150`.

## File map

- `av_ir231_poly.py` and `.cpp`: independent reference implementations of the
  fixed-`d` family recurrence; the Python version includes brute force.
- `av12453_poly.py` and `.cpp`: unreduced two-threshold kernels.
- `av12453_reduced.py`: first-coordinate quotient with a cross-check against
  the full Python recurrence.
- `av12453_fast.cpp`: scalar optimized implementation and utilities used by
  the packed frontend.
- `av12453_fast_rns.cpp`: eight-prime AVX-512/OpenMP production kernel.
- `reconstruct_av12453_rns.py`: CRT reconstruction, exact bound, redundant
  residues, independent modulus, and prefix checks.
- `av12453_scalar_residue_parallel.cpp`: separately written 61-bit verifier.
- `av12453_dense_mod_verify.cpp`: dense verifier that omits the second
  quotient and prefix-scan optimization.
- `av12453_bound_certificate.cpp`: standalone exact audit of the CRT bound.
- `av12453_asymptotic_holdout.py`: dependency-free reproduction of the frozen
  fit on `n=70,...,100` and its `n=101,...,150` holdout diagnostics.
- `av12453_n300/`: the faster GEMM-structured engine, harness and independent
  reference for the `n <= 300` computation, plus the cluster package.
- `walkthrough/`: a permuta-based walkthrough of the paper's definitions and
  examples, section by section, for reading and experimenting (not part of
  the verification chain).
- `av12453_sampler/`: uniform random sampling from `Av_n(12453)` by the
  recursive method on the paper's reduced kernel tables, with validation and
  the PermPAL-style heatmaps shown in the paper (`examples/ex_n300_1M`).
- `data/`: exact coefficient and profile data.
- `certificates/`: packed residues, independent residues, and recorded run
  logs used by the deterministic `N=150` certificate.

See `av12453_fast_README.md` for the scalar exact implementation and
`av12453_fast_rns_README.md` for full residue-pack reproduction.
