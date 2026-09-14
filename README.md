# Protected tails and polynomial-time enumeration of Av(12453)

Companion repository for the paper

> Henning Ulfarsson, *Protected tails and polynomial-time enumeration of
> permutations avoiding a direct sum of an increasing pattern and 231*, 2026.
> Preprint; arXiv identifier to be inserted.

Repository: <https://github.com/ulfarsson/public-12453>

The paper gives an exact algorithm that counts the permutations avoiding a
pattern `beta_d = 12...d (+) 231` (direct sum), for every fixed `d`, in
polynomially many arithmetic operations.  The first members of the family are
`1342` and `12453`.  For `12453` the algorithm runs in `O(N^7)` operations
with `O(N^4)` stored integers, and the repository contains the programs that
implement it, a certified computation of the counting sequence through
`n = 150` (extended to `n = 300` by a faster engine), a uniform random
sampler with the heatmap of the paper, a walkthrough of the paper with
exhaustive checks of its statements for length at most 8, and a Lean 4
development that machine-checks the counting recurrences for `d <= 2`.

## Layout

| path | contents |
|---|---|
| `paper/` | the manuscript (`av12453_polytime.tex`, `.bib`, `figures/`) and its PDF |
| `code/` | the paper's algorithm and the certificate programs, see `code/README.md` |
| `code/av_ir231_poly.py`, `.cpp` | the family recurrence for `Av(iota_r (+) 231)`; the Python version has a brute-force check |
| `code/av12453_poly.py`, `.cpp` | the unreduced two-threshold kernels for `12453` |
| `code/av12453_reduced.py` | the first-coordinate quotient (Section 7 of the paper) |
| `code/av12453_fast.cpp`, `code/av12453_fast_rns.cpp` | optimized scalar and eight-prime AVX-512 programs used for the `n = 150` certificate |
| `code/reconstruct_av12453_rns.py` | exact Chinese-remainder reconstruction with bound, redundancy and prefix checks |
| `code/av12453_scalar_residue_parallel.cpp`, `code/av12453_dense_mod_verify.cpp`, `code/av12453_bound_certificate.cpp` | independently written verifiers |
| `code/data/` | the exact terms `a_0, ..., a_150` (certified) and `a_0, ..., a_300` |
| `code/certificates/` | residue files of the certificate runs |
| `code/av12453_n300/` | the faster engine, harness and pure-Python reference that produced the terms to `n = 300` |
| `code/av12453_sampler/` | uniform random sampler for `Av_n(12453)`, heatmap tools, the examples shown in the paper |
| `code/walkthrough/` | a permuta-based walkthrough of the paper and the exhaustive checks of its statements for `n <= 8` |
| `formal/` | the Lean 4 development, its build and audit script `check.sh`, `README.md` and an audit report |
| `MANIFEST.sha256` | SHA-256 digests of every file in this repository |

## Requirements

- A C++20 compiler; the programs were built with `g++` 14 with OpenMP.  The
  packed certificate program `av12453_fast_rns.cpp` additionally needs
  AVX-512F/DQ; everything else is portable.
- Python 3.11 or later.  PyPy is recommended for the pure-Python programs
  (the walkthrough checks take about one minute under PyPy).
- `permuta` 2.3.1 (`pip install permuta`) for the walkthrough and its checks.
- Lean 4.33.1 through `elan`, with the Mathlib revision pinned in
  `formal/Av12453/lake-manifest.json`, for the Lean development.

All commands below are run from the repository root.

## Reproducing the results

### Exhaustive checks of the paper's statements for n <= 8

Every numbered statement of the paper that has finite content is compared
with a brute-force computation from the definitions, over all permutations
of length at most 8 (about six million comparisons, one minute under PyPy):

```sh
python3 -m venv venv && venv/bin/pip install permuta      # or a PyPy venv: pypy3 -m venv venv
venv/bin/python3 code/walkthrough/av12453_exhaustive_checks.py --nmax 8
```

The script prints one line per statement and exits with status 1 if any
comparison fails.  The walkthrough itself,
`code/walkthrough/av12453_walkthrough.py`, runs the paper's examples section
by section; see `code/walkthrough/README.md`.

### The paper's algorithm on small n

The reference implementations include brute-force cross-checks:

```sh
pypy3 code/av_ir231_poly.py 1 8 --verify-small 8     # Av(1342), family recurrence
pypy3 code/av_ir231_poly.py 2 8 --verify-small 8     # Av(12453)
pypy3 code/av12453_poly.py 12 --verify-small 8        # unreduced kernels
pypy3 code/av12453_reduced.py 10 --verify             # first-coordinate quotient against av12453_poly.py
```

The optimized program computes the terms to a given `N`:

```sh
g++ -O3 -DNDEBUG -march=native -std=c++20 -pthread code/av12453_fast.cpp -o av12453_fast
./av12453_fast 100 --threads 4 --output av12453_terms_0_100.txt
```

### The certified terms through n = 150

The certified file is `code/data/av12453_terms_0_150.txt`, SHA-256
`f5ab4017ec65a661d8fbcd84d2f7893afe5e2c695dd082ace58399f7960340fc`.
To reconstruct it from the saved residues (exact Chinese remainder theorem
with the proved bound, six redundant primes and one independent modulus):

```sh
python3 code/reconstruct_av12453_rns.py \
  code/certificates/av12453_residues_150_pack0.txt \
  code/certificates/av12453_residues_150_pack1.txt \
  code/certificates/av12453_residues_150_pack2.txt \
  --primary-count 18 \
  --independent-residue 2305843009213693951:code/certificates/av12453_residue_150_mersenne.txt \
  --known-prefix code/data/av12453_terms_0_100.txt \
  --output av12453_reconstructed_terms.txt
```

The expected final line is
`reconstructed=151 primary=18 redundant=6 independent=1 bound_bits=558 product_bits=558`.
Recomputing the residue packs themselves (`code/av12453_fast_rns.cpp`) took
about 28 minutes per pack on an AVX-512 machine; see `code/README.md`.
The frozen asymptotic fit of Section 10 and its holdout are reproduced by
`python3 code/av12453_asymptotic_holdout.py code/data/av12453_terms_0_150.txt`.

### The terms through n = 300

`code/data/av12453_terms_0_300.txt` was produced by the engine and harness in
`code/av12453_n300/` (residues modulo 77 primes below `2^16`, reconstructed
from the 71 largest with the same injection bound, the remaining six
withheld as a check).  `code/av12453_n300/README.md` describes the pipeline,
the independent pure-Python reference `pyref/ref.py`, and the validation.

### Uniform random sampling and the heatmap

```sh
cd code/av12453_sampler
sh build_tables.sh && sh build_sampler.sh
./tables --N 100 --threads 4 --out N100.avr
./sampler --table N100.avr --n 100 --count 20000 --seed 1 --threads 4 --out s100.txt
python3 heatmap.py s100.txt -o examples/ex_n100
./avoid_check s100.txt
```

`README.md` in that directory documents the table format, the scaled tables
needed for `n > 276`, the validation performed, and the one-million-sample
heatmap of length 300 shown in the paper (`examples/ex_n300_1M*`).

### The Lean development

```sh
export PATH="$HOME/.elan/bin:$PATH"
sh formal/check.sh
```

This builds the twenty modules (about nine minutes cold), runs the axiom
sweep over every declared constant, and rejects any `sorry`, `native_decide`
or non-standard axiom; it ends with `CERTIFICATE CHECK PASSED`.  The four
main theorems, the definitions a reader should check by eye against the
paper, and the trusted base are listed in `formal/README.md` and
`formal/AUDIT_2026-09-05.md`.  The toolchain and the Mathlib revision are
pinned; do not run `lake update`.

## Verifying the files

```sh
sha256sum -c MANIFEST.sha256
```

## Data and licensing

The code, data and Lean development are released under the Apache License
2.0 (see `LICENSE`).  The text and figures of the paper in `paper/` are
copyright the author.

## Citing

See `CITATION.cff`.  Until the arXiv identifier is available:

```text
H. Ulfarsson, Protected tails and polynomial-time enumeration of permutations
avoiding a direct sum of an increasing pattern and 231, preprint, 2026.
Code and data: https://github.com/ulfarsson/public-12453
```
