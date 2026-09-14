# Packed exact computation of `Av(12453)`

This bundle computes the exact coefficients

\[
a_n=|\operatorname{Av}_n(12453)|
\]

through a requested cutoff.  The `N=150` output contains 151 terms, including
`a_0=1`.

## Files

- `av12453_fast.cpp`: scalar utilities, compressed layout, and reference
  implementation used by the packed front end.
- `av12453_fast_rns.cpp`: eight-lane AVX-512 residue kernel with OpenMP
  row-level parallelism and pack checkpoints.
- `reconstruct_av12453_rns.py`: exact CRT reconstruction, bound certificate,
  redundant-prime checks, and optional known-prefix check.
- `av12453_scalar_residue_parallel.cpp`: independent 61-bit scalar verifier.
- `av12453_bound_certificate.cpp`: standalone exact upper-bound audit.
- `data/av12453_terms_0_150.txt`: certified coefficients.
- `certificates/`: saved residue packs, logs, and the scalar check.
- `../notes/av12453_150_computation_report.md`: method, timings, hashes, and
  checks.

## Quick reproduction

```sh
g++ -O3 -DNDEBUG -march=native -std=c++20 -fopenmp \
  av12453_fast_rns.cpp -o av12453_fast_rns

for pack in 0 1 2; do
  ./av12453_fast_rns 150 --threads 5 --residues-only \
    --pack-index "$pack" \
    --output "certificates/av12453_residues_150_pack${pack}.txt"
done

python3 reconstruct_av12453_rns.py \
  certificates/av12453_residues_150_pack0.txt \
  certificates/av12453_residues_150_pack1.txt \
  certificates/av12453_residues_150_pack2.txt \
  --primary-count 18 \
  --independent-residue \
    2305843009213693951:certificates/av12453_residue_150_mersenne.txt \
  --output data/av12453_terms_0_150.txt
```

Omit `--independent-residue` until the scalar verification file has been
computed; it is an extra check, not an input to CRT reconstruction.

The vector executable requires AVX-512F and AVX-512DQ (or a compatible
compiler target selected by `-march=native`).  One `N=150` pack stores about
684 MB of residue table data, plus its boundary mirror and metadata.  Packs
are independent and may be computed on different machines.

The output of each executable is written through a temporary path and renamed
only on success.  `--pack-index 0`, `1`, or `2` limits a residue run to one
restartable eight-prime pack.  Omit `--pack-index` to run all required packs
sequentially.

For the mathematical recurrence, state compression, operation counts,
certificate, and independent checks, see
`../notes/av12453_150_computation_report.md`.
