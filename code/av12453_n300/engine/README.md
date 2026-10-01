# `engine/`: GEMM realization of the homogeneous split

This directory holds the engine that computed `|Av_n(12453)| mod p` for
`n <= 300` and the 77 primes of `../harness/primes_u16.txt`.  It evaluates
the reduced `d = 2` recurrence of the paper (`../../../paper/av12453_polytime.tex`,
Section 7) with the homogeneous split proved in
`../../../notes/av12453_speedup_proofs.tex`, organized as dense matrix
products that are exact in binary64.  The modulus is a compile-time
constant, so a CRT sweep uses one binary per prime.

There are two versions, with bit-identical output:

- **v1**, `av12453_gemm_split_v1.cpp`, produced every residue file in
  `../../certificates/av12453_residues_300/`.  The source compiled for that
  computation has SHA-256
  `a617f2dce15d9b7d0452281b0d459d81bd3bdca37492e399673e674c5afa5646`.  The
  file here differs from it in one line, line 774, the default `--truth`
  path: it was an absolute path on the machine that ran the computation and
  is now `code/data/av12453_terms_0_150.txt`, relative to the repository
  root.  The file as published has SHA-256
  `cbd713692b803d4551bd55385082684e8d824641a4c2c587c0c634c2ee0c0b37`.
- **v2**, `av12453_gemm_split_v2.cpp`, is recommended for new runs.  It is v1
  plus a parallel empty-stack phase, a hardened `CERTIFY`, a warning-free
  build under `-Wall -Wextra` and a tested `-DUSE_CBLAS` path (§10); the
  split kernel, the interpolation, the absorption and all arithmetic are
  unchanged.  `build.sh` and `build_primes.sh` compile v2.

Both versions print `engine av12453_gemm_split` in their banner and in the
residue-file header.  Their header comments say that they are derived from
`av12453_homog_split.cpp`, an earlier single-modulus implementation of the
same homogeneous split that is not part of the published repository; below
it is called "the earlier engine".  Everything except the split kernel is
carried over from it: the band and `D` terms, the inverse-Vandermonde
interpolation, the absorption of a finished grade into `E`, the empty-stack
phase, `CERTIFY`, the support check, `--dump-r`, the literal-split reference
engine (`--engine naive|both`) and the instrumented counters.

| file | content |
|---|---|
| `av12453_gemm_split_v1.cpp` | engine v1 (single source, 968 lines) |
| `av12453_gemm_split_v2.cpp` | engine v2 (single source, 1060 lines) |
| `build.sh` | builds the test flavours of v2 into `bin/` (§7), after checking that every hard-wired modulus is prime |
| `build_primes.sh` | builds one v2 binary per prime of a prime list, with Linux and macOS recipes (§10.5) |
| `RUN_ON_LAPTOP.md` | the whole pipeline: primes, build, sweep, reconstruction, resuming |
| `rusage_run.c` | `fork`/`wait4` stand-in for `/usr/bin/time`: wall clock, peak RSS and exit status of a command |
| `cblas_stub/` | `cblas.h` and `cblas_ref.c`: a minimal CBLAS header and a naive reference `cblas_dgemm`, used only to test the `-DUSE_CBLAS` path |

---

## 1. The recurrence

```
R[l][a][q][s] = sum_{h<a} R[l][h][a+q-h-1][s]                    (BAND1)
              + sum_{r<q} R[l+q-r-1][a][r][s]                    (BAND2)
              + (l==1 ? [a==0 && q==s] : 2 R[l-1][a][q][s])      (D)
              + SPLIT[l][a][q][s]
SPLIT[l][a][q][s] = sum_{l1+l2=l-1} sum_{a1+a2=a} sum_m R[l1][a1][q][m] R[l2][a2][m][s]
```

with `l >= 1`, `a, q >= 0`, `l+a+q <= N`, `s < slen(a,q) = (a==0 ? q+1 : a+q)`
and `l1, l2 >= 1` in the split; this is `eq:R-recurrence` of the paper with
`R[l][a][q][s] = R_{l,a}(q,s)`.

With the offset grade `t = l+a` and the slice polynomials
`C_t(y;u,v) = sum_{a<t} y^a R[t-a][a][u][v]` (stored evaluated at `y = y_j` as
`E[j][t][u][v]`, row length `scount(t,u) = (t==1 ? u+1 : t+u-1)`), homogeneity
gives, for output grade `W` and every point `y_j`,

```
Phi_W(y_j;q,s) = sum_{tau1=1}^{W-2} sum_m E[tau1-q][q][m] * E[W-1-tau1][m][s]
               = sum_a y_j^a SPLIT[W-q-a][a][q][s].
```

The earlier engine evaluates this double sum with an `axpy` over one scalar
at a time and one Barrett fold per product.  This engine evaluates it as a
dense matrix product with no modular reduction inside.

## 2. The GEMM formulation

Fix a grade `W` and a point `j`.  For every `g2 = 1, ..., W-2` put
`tau1 = W-1-g2` and

* `A` = `tau1 x tau1`, `A[q][m] = C_{tau1-q}(y_j;q,m)`, `q = 0..tau1-1`: all
  slices of grade `tau1`.  Row `q` carries `scount(tau1-q,q)` entries, that is
  `tau1-1` for `q < tau1-1` and `tau1` for `q = tau1-1`; the rest is zero
  padding.
* `B` = `tau1 x (W-2)`, `B[m][s] = C_{g2}(y_j;m,s)`: an upper staircase, row
  `m` carrying `scount(g2,m)` entries, so the row lengths grow by one per row.

Then `Phi_W(y_j) = sum_{g2} A·B`, accumulated into one `(W-2) x (W-2)`
buffer `C`.

The range of `g2` includes `g2 = W-2`, that is `tau1 = 1`, whose `A` is the
`1 x 1` matrix `A[0][0] = C_1(y;0,0) = R[1][0](0,0) = 1`; this block
contributes `C_{W-2}(y;0,s)` to `Phi_W(y;0,s)`.  A build whose loop stops at
`g2 = W-3` fails `CERTIFY` at `n = 5` (118 instead of 119).

Three exact reductions of the work:

1. **Row pruning.**  `SPLIT[l][...] = 0` for `l < 3` (the split needs
   `l1, l2 >= 1`), so `deg_y Phi_W(·;q,·) <= W-q-3`, and coordinate `q` needs
   exactly the `W-q-2` points `y = 1..W-q-2`.  Equivalently, the point
   `y = j` (1-based) is needed only for the rows `q <= W-2-j` of `A`, that is
   for `M = min(tau1, W-1-j)` rows.  With `--prune` the engine evaluates
   exactly these rows and interpolates coordinate `q` from `W-q-2` points
   (in the source the point index is 0-based, `y = j+1`, and the row count
   reads `min(tau1, W-2-j)`).  The earlier engine's
   `--prune` uses `W-q` points per coordinate, two more than necessary; both
   rules are exact, and the difference makes the structural multiply-add
   counts of the two engines differ by about 2 %.  The degree check of the
   unpruned runs (§6) tests the degree bound on which the sharper rule rests.
2. **Staircase column blocks.**  `B` is packed one `NCB = 64`-wide column
   block at a time, and each block starts at the first row that reaches it,
   `mstart(s0) = (g2 == 1 ? s0 : max(0, s0+2-g2))`.  Only the `NR`-wide tail
   of a block wastes multiplications, so the padding overhead is `O(NR)` per
   row instead of `O(tau1)`.
3. **Zero-row padding** of `A` up to a multiple of `MR = 4` (at most 3 wasted
   rows).

With this packing the engine issues `1.882e13` FMA multiply-adds at `N = 300`
against a structural requirement of `1.5623e13`, a factor **1.205** (§8.2).

### Micro-kernel

`MR x NR = 4 x 8` accumulators in 16 NEON `float64x2_t` registers, `K`-loop
over `m` with four `fmla vD.2d, vB.2d, vA.d[0]`-style scalar-broadcast FMAs
per accumulator row (`vfmaq_n_f64`).  `A` is packed row-major (`MR` rows of
`K` doubles), `B` block-packed `(K-mstart) x ncPad`.  The NEON kernel is
compiled on aarch64; elsewhere, and with `-DNO_NEON`, the portable C version
of the same 4 x 8 kernel is used.  gcc 14.2 `-O3 -march=native`
auto-vectorizes the portable version to within 1.5 % of the intrinsics
(`N = 150`, 8 threads: 4.075 s against 4.044 s, 21.74 against
22.06 Gmadd/s/thread).  `-DUSE_CBLAS` replaces the blocked kernel by one
`cblas_dgemm` per `(j, g2)` on the same packed double panels; this path drops
the staircase blocking and computes the full `MPb x nsPad x K` product
(§10.4).

## 3. Exactness of each build

Storage width is a compile-time choice: `u16` for `P < 2^16` and `u32`
otherwise (`-DSTORE_BITS=16|32` overrides it); a `static_assert` enforces
`P < 2^21`.  Everything that enters the GEMM is a residue in `[0,P)`, and the
accumulator is IEEE binary64, in which every integer below `2^53` is exact
and integer `+` and `*` on such values are exact.

Let `PRODLIMIT = floor(2^53 / (P-1)^2)`, the number of products that can be
summed before the accumulator can leave the exact range.  The engine tracks,
for every `C` entry, an upper bound on the number of products accumulated
since the last reduction (the sum of the inner dimensions `tau1` of the `g2`
blocks done so far) and reduces `C` modulo `P` whenever the next block could
push it past `PRODLIMIT`.  Each reduction leaves values `< P`, which is
charged as one product.

| build | `P` | storage | `(P-1)^2` | `PRODLIMIT` | products per `C` entry, `N = 300` | reductions per `(W,j)` |
|---|---|---|---|---|---|---|
| `gemm_u16_65521` | 65521 | `u16` | `< 2^32` | 2 098 176 | `sum_{tau1=1}^{W-2} tau1 <= 44 551` | 1 (the final one) |
| `gemm_u16_65519` | 65519 | `u16` | `< 2^32` | 2 098 304 | same | 1 |
| `gemm_u32_2097143` | 2097143 | `u32` | `< 2^42` | 2 048 | same | about `W^2/(2·2048)`, at most 22 at `W = 300` |
| `gemm_u32_2097133` | 2097133 | `u32` | `< 2^42` | 2 048 | same | at most 22 |

So for the two 16-bit primes a whole grade accumulates without an
intermediate reduction (`44 551 · 2^32 < 2^48.5 < 2^53`), and for the two
21-bit primes the periodic reduction keeps the accumulator below
`2048 · 2^42 = 2^53`.  Both bounds are static: `static_assert(PRODLIMIT >= 64)`
and the runtime counter enforce them, so any other prime `P < 2^21` given as
`-DMODP` is covered by the same argument.

The reduction of an exact non-negative integral double `x < 2^53` uses
`r = x - P·floor(x·(1/P))` followed by two conditional corrections;
`floor(x·(1/P))` differs from `floor(x/P)` by at most 1 because the relative
error of the product is at most `2^-52` and `2^53/P · 2^-52 < 1`.  Every binary
tests itself: each run compares this reduction with integer `%` on 200 000
pseudo-random values below `2^53` and on the boundary values, and exits
non-zero on any disagreement (the `selftest: OK` line).

The `--dump-r`, interpolation, band, absorption and empty-stack code paths
use 64-bit Barrett integer arithmetic, as in the earlier engine.

`-DUSE_CBLAS` keeps the same bounds: `cblas_dgemm(..., beta = 1.0)`
accumulates into the same `C` in binary64, and the driver loop reduces on the
same `PRODLIMIT` schedule (§10.4).  Since every partial sum is an integer
below `2^53`, every partial sum is exact and the result does not depend on
the order of accumulation; this is why a BLAS, or the naive reference in
`cblas_stub/`, reproduces the blocked kernel bit for bit.

## 4. Memory model

`E` (the evaluated slice table) dominates.  The sizes below are exact
counts.

```
ESIZE  = sum_{t=1..N} sum_{u=0..N-t} scount(t,u)
points = N-2 with pruning (the 1-based point j is used only from grade j+2 on),
         N+1 without
RSIZE  = sum_{w=1..N} [ w(w+1)/2 + (w-1)w(2w-1)/6 ]  =  N(N+1)(N^2+N+4)/12
```

(`RSIZE` is the stored-entry count `eq:d2-first-reduced-counts` of the paper.)

| `N` | `ESIZE` | points | `E` entries | `E` u16 | `E` u32 | `RSIZE` | `R` u16 | `R` u32 |
|---|---|---|---|---|---|---|---|---|
| 150 | 1 125 100 | 148 | 166 514 800 | 333 MB | 666 MB | 42 759 425 | 86 MB | 171 MB |
| 200 | 2 666 800 | 198 | 528 026 400 | 1.06 GB | 2.11 GB | 134 683 400 | 269 MB | 539 MB |
| **300** | **9 000 200** | **298** | **2 682 059 600** | **5.364 GB** | **10.728 GB** | **679 537 600** | **1.359 GB** | **2.718 GB** |

Without pruning all `N+1 = 301` points are stored at `N = 300`, that is
`2 709 060 200` entries; the three points that pruning removes save
`27 000 600` entries.

Everything else at `N = 300`: the inverse Vandermonde matrices,
`sum_{n<=298} n^2 = 8 865 649` `u32` = **35.5 MB**; the per-grade buffer of
evaluated split values `Cbuf`, `298·298·298 = 26 463 592` entries =
**52.9 MB** (`u16`) / **105.9 MB** (`u32`); the per-thread GEMM scratch (`A`,
`B`, `C` double panels), `< 2.5 MB` x 8 threads = **20 MB**; the `G` table of
the empty-stack phase, `301^2` `u32` = 0.4 MB.

`R` is not needed in full during the transfer: `bands(w)` reads only grade
`w-1`, and `split`/`absorb` only grade `w`.  Two rolling grade buffers
therefore suffice (`max_w GS(w) = 9 000 200` entries at `N = 300`, that is
**18 MB** `u16` / **36 MB** `u32`).  With `--spill` the engine keeps exactly
those two buffers and appends each finished grade to a file; before the
empty-stack phase, which needs all grades, it frees `E`, `Wpre` and `Cbuf`
and reads the file back into one contiguous `R`.

Peaks at `N = 300` (measured, `--prune`, 8 threads):

| build | mode | predicted peak | measured peak RSS |
|---|---|---|---|
| `u16`, `P = 65521` | `R` in RAM | `5.364 + 1.359 + 0.09` = 6.81 GB | **6 521.6 MiB = 6.84 GB** |
| `u32`, `P = 2097143` | `--spill` | transfer `10.728 + 0.036 + 0.14` = 10.90 GB; extraction `2.718` GB | **10 460.2 MiB = 10.97 GB** |
| `u32`, `P = 2097143` | `R` in RAM (not run at `N = 300`) | `10.728 + 2.718 + 0.14` = 13.59 GB | |

Without `--spill` the `u32` build at `N = 300` would need
`10.728 + 2.718 = 13.4 GB` for `E` and `R` alone, which is why the spill path
exists.

## 5. File formats

**Residue file** (`--out FILE`):

```
# prime 65521 300
# engine av12453_gemm_split storage u16 threads 8 prune 1
0 1
1 1
...
300 <residue>
```

Header lines start with `#`; the body is `n residue` for `n = 0..N`,
consecutive.  This is the format that `../harness/residue_io.py` checks and
`../harness/reconstruct.py` reads; `../../reconstruct_av12453_rns.py
--independent-residue P:PATH` reads it as well (it skips `#` lines).

**Sidecar** (`--sidecar FILE`): one JSON object with `prime`, `storage`, `N`,
`threads`, `prune`, `spill`, `wall_s`, `transfer_s`, `split_s`, `interp_s`,
`absorb_s`, `bands_s`, `extract_s`, `peak_rss_kib`, all instrumented counters
(`split_madds_structural`, `split_madds_issued`, `pack_a`, `pack_b`,
`reduce_ops`, `interp_madds`, `absorb_madds`, `empty_stack_madds`,
`band_adds`), `gemm_madds_per_s_total`, `gemm_madds_per_s_per_thread`,
`E_entries`, `R_entries`, `residue_fnv1a64` (FNV-1a of the residue vector),
`certify`, `certify_upto`, `exit_code`; v2 adds `empty_stack_wall_s`,
`empty_stack_cpu_s` and `total_cpu_s`.

**R dump** (`--dump-r FILE`): `# P <prime> N <N>`, then one line
`l a q s value` per non-zero entry, in the order `l = 1..N`, `a = 0..N-l`,
`q = 0..N-l-a`, `s = 0..slen-1`.  The earlier engine's `--dump-r` writes the
same format, and after the header line it is the format of
`../pyref/ref.py --dump-r` (§9).

**Spill file** (`--spill-file FILE`, default `r_spill.bin`): raw `ST`
(`uint16_t`/`uint32_t`) grade blocks appended in grade order, grade `w`
occupying `GS(w) = w(w+1)/2 + (w-1)w(2w-1)/6` entries, each grade laid out by
`l = 1..w`, then `a = 0..w-l`, row length `slen(a,w-l-a)`.  It is exactly the
concatenation of the in-RAM `R`, so the read-back is one `fread`.

**Exit status.**  0 if every check passed; 1 if the binary64-reduction
self-test, the support check, the degree check, the evaluation check,
`CERTIFY` or the `--engine both` table match fails; 2 for a usage error, a
file that cannot be opened, read or written, and (v2) a `--truth` file that
is too short or malformed.

## 6. Built-in checks

| check | when | what it asserts |
|---|---|---|
| `selftest` | every run | the binary64 `mod P` used inside the GEMM equals integer `%` on 2·10^5 random values `< 2^53` and on the boundary values |
| `support-check` | every `--engine gemm` run | no interpolated split value lands outside `s < slen(a,q)` |
| `degree-check` | unpruned runs | no interpolated `y^a` coefficient with `a > W-q-3` is non-zero (the fact that makes the row pruning exact) |
| `eval-check` | unpruned runs | the two evaluation points *not* used by the interpolation reproduce the interpolant by Horner, an independent test of the homogeneity identity |
| `CERTIFY` | every run | `a_n mod P` equals the `--truth` file (by default the certified `code/data/av12453_terms_0_150.txt`) for `n <= min(N,150)` |
| `TABLE-MATCH` | `--engine both` | the full `R` table equals that of the literal-split engine in the same binary |

## 7. Command line and builds

```
av12453_gemm_split --n N [--engine gemm|naive|both] [--threads K] [--prune]
                   [--spill [--spill-file F]] [--dump-r FILE]
                   [--out RESIDUES] [--sidecar FILE] [--truth FILE]
```

* `--prune` turns on the sharp degree pruning (recommended; `N-2` evaluation
  points).  Without it (the default, also `--no-prune`) every one of the
  `N+1` points is evaluated for every coordinate and the degree and
  evaluation checks run.
* `--truth FILE` names the file of exact terms for `CERTIFY`.  The default,
  `code/data/av12453_terms_0_150.txt`, is resolved against the working
  directory, so it is found only when the binary runs from the repository
  root; from anywhere else pass the path, for example
  `--truth ../../data/av12453_terms_0_150.txt` from this directory.
* `--spill` is incompatible with `--dump-r` and with `--engine naive|both`
  (both need the whole table in RAM).
* `--engine naive` runs only the literal-split engine; `--engine both` runs
  the GEMM engine and the literal split and compares the full tables.
* Defaults: `--n 40`, `--threads 1`, `--engine gemm`.

Compile-time options:

```
-DMODP=<prime>          modulus, must be < 2^21 (default 65521)
-DSTORE_BITS=16|32      storage width (default: 16 iff MODP < 2^16)
-DNO_NEON               portable micro-kernel instead of the NEON one
-DUSE_CBLAS             one cblas_dgemm per (j, g2) on the packed panels
-DNO_PARALLEL_EXTRACT   (v2 only) the serial v1 empty-stack loop, a timing control
```

A single binary:

```bash
g++ -O3 -march=native -std=c++17 -fopenmp -funroll-loops -Wall -Wextra \
    -DMODP=65521ull av12453_gemm_split_v2.cpp -o av12453_gemm_65521
```

`./build.sh` builds into `bin/`: `gemm_u16_65521`, `gemm_u16_65519`,
`gemm_u32_2097143`, `gemm_u32_2097133`, `gemm_u32_65521` (`u32` storage with a
16-bit prime, a storage-path cross-check), `gemm_portable_65521`
(`-DNO_NEON`), `gemm_modp` (the prime in `$MODP`, default 65521), and
`gemm_cblas_65521` and `gemm_cblas_2097143` (`-DUSE_CBLAS` against
`cblas_stub/`; with `USE_SYSTEM_CBLAS=1` it builds `gemm_cblas_65521`
against a system OpenBLAS instead).  `build_primes.sh` (§10.5) builds the
per-prime binaries `av12453_gemm_<prime>` that `../harness/run_all.sh`
expects.  `rusage_run` is built by hand, `cc -O2 -o bin/rusage_run
rusage_run.c`; then `bin/rusage_run CMD ARGS...` prints the wall time, peak
RSS and CPU times of `CMD` on stderr and returns its exit status.

## 8. Measurements of v1

Machine: Lima VM on an Apple Silicon laptop (aarch64 Linux, 9 visible CPUs
with an 8-CPU quota, 16 GiB RAM), g++ 14.2.0,
`-O3 -march=native -std=c++17 -fopenmp -funroll-loops`.  Times are wall clock
from `rusage_run`; peak RSS is the child's `ru_maxrss` from `wait4`.  All runs
use `--prune` unless stated.

### 8.1 Benchmarks

| `N` | build | threads | wall (s) | split (s) | interp (s) | absorb (s) | extract (s) | peak RSS (MiB) | Gmadd/s/thread |
|---|---|---|---|---|---|---|---|---|---|
| 100 | u16 `P=65521` | 1 | 2.40 | 1.39 | 0.32 | 0.53 | 0.13 | 85.4 | 21.5 |
| 100 | u16 `P=65521` | 8 | 0.48 | 0.20 | 0.04 | 0.08 | 0.13 | 88.5 | 18.7 |
| 100 | u32 `P=2097143` | 1 | 2.60 | 1.49 | 0.33 | 0.57 | 0.17 | 165.8 | 20.0 |
| 100 | u32 `P=2097143` | 8 | 0.54 | 0.21 | 0.05 | 0.09 | 0.17 | 168.4 | 18.0 |
| 150 | u16 `P=65521` | 1 | 22.40 | 14.36 | 2.47 | 3.83 | 1.64 | 414.0 | 22.7 |
| 150 | u16 `P=65521` | 8 | 4.77 | 2.06 | 0.38 | 0.55 | 1.69 | 419.4 | 19.8 |
| 150 | u32 `P=2097143` | 1 | 23.92 | 14.96 | 2.41 | 3.93 | 2.45 | 819.4 | 21.8 |
| 150 | u32 `P=2097143` | 8 | 5.62 | 2.09 | 0.35 | 0.63 | 2.39 | 825.3 | 19.5 |
| 200 | u16 `P=65521` | 8 | 23.52 | 10.68 | 1.50 | 2.33 | 8.70 | 1 303.6 | 20.5 |
| 200 | u32 `P=2097143` | 8 | 31.50 | 12.73 | 1.94 | 3.67 | 12.27 | 2 582.0 | 17.2 |
| 200 | u32 `P=2097143` `--spill` | 8 | 26.74 | 10.38 | 1.43 | 2.30 | 10.84 | 2 088.1 | 21.1 |
| **300** | **u16 `P=65521`** | **8** | **198.98** | **106.53** | **10.63** | **15.65** | **63.50** | **6 521.6** | **22.1** |
| **300** | **u32 `P=2097143` `--spill`** | **8** | **225.16** | **107.80** | **10.86** | **18.13** | **81.91** | **10 460.2** | **21.8** |

The `extract` column is the empty-stack phase together with the release of
`E` (and, with `--spill`, the read-back of `R`).  In v1 the empty-stack phase
is serial, and it is almost all of the 63.50 s `extract` time of the
`N = 300` u16 run, 32 % of the total.  v2 parallelizes it (§10.1).

### 8.2 Instrumented multiply-adds

`structural` counts the multiply-adds the split must do (the same definition
as the earlier engine's `split madds structural`); `issued` counts the FMA
slots the GEMM actually executes, including staircase and `MR` padding.

| `N` | structural | issued | issued/structural | structural / `(N^6/24)` |
|---|---|---|---|---|
| 100 | 19 924 528 568 | 29 902 907 808 | 1.501 | 0.478 |
| 150 | 235 381 173 728 | 325 738 808 704 | 1.384 | 0.496 |
| 200 | 1 346 818 281 138 | 1 752 053 397 536 | 1.301 | 0.505 |
| 300 | 15 622 561 507 708 | 18 819 551 098 976 | 1.205 | 0.514 |

Unpruned (`N = 150`): structural `446 984 370 494`, issued
`623 043 607 808`.  So the degree pruning removes 47 % of the structural work
(`1 - 235 381 173 728/446 984 370 494 = 47.3 %`), and the GEMM padding
overhead falls from 1.50 at `N = 100` to 1.20 at `N = 300` (it is
`O(NR/tau1)` per row block).

Other counters at `N = 300`: `pack A` 101 073 438 600 and `pack B`
184 762 592 672 element conversions (1.5 % of the FMA count), `interp`
158 982 693 805 modular multiply-adds, `absorb` 202 502 204 800, empty-stack
40 502 249 970, band adds 2 011 612 200.  The `u16` build performs
1 012 456 192 binary64 element reductions of `C` (one pass per `(W,j)`); the
`u32` build performs 15 984 316 864 (the `PRODLIMIT = 2048` schedule), about
0.085 % of the issued FMA count.

### 8.3 Thread scaling (`N = 150`, u16 `P = 65521`, `--prune`)

| threads | wall (s) | split (s) | Gmadd/s (all) | Gmadd/s/thread | speed-up (wall) |
|---|---|---|---|---|---|
| 1 | 21.89 | 14.22 | 22.91 | 22.91 | 1.00 |
| 2 | 11.73 | 7.21 | 45.17 | 22.59 | 1.87 |
| 4 | 6.80 | 3.69 | 88.22 | 22.05 | 3.22 |
| 8 | 4.13 | 1.89 | 172.8 | 21.59 | 5.30 |

The GEMM phase itself scales 7.52x on 8 threads; the whole-run 5.30x is
limited by the serial empty-stack phase (1.2-1.3 s at `N = 150`).

### 8.4 Comparison with the earlier engine

Same machine and flags, both engines with `--prune` (the earlier engine in
its `--engine saprime` mode):

| run | earlier engine | this engine | ratio |
|---|---|---|---|
| `N = 150`, 1 thread, `P = 2^31-1` (its fastest modulus, Mersenne fold) | **47.48 s**, 844.7 MiB | 21.89 s, 414.0 MiB (u16) / 23.92 s, 819.4 MiB (u32) | **2.17x** faster, 2.0x less RAM |
| `N = 150`, 1 thread, `P = 65521` (same prime, Barrett) | **172.98 s**, 844.7 MiB | 21.89 s, 414.0 MiB | **7.90x** |
| `N = 200`, 8 threads, `P = 65521` (same prime) | **154.04 s**, 2 639.4 MiB | 23.53 s, 1 303.6 MiB | **6.55x**, 2.0x less RAM |

**Kernel throughput.**  On the same machine the earlier engine's split runs at
about `5.7e9` multiply-adds per second per thread (one thread, `N = 150`); in
the first run of the table it executed `2.413e11` split multiply-adds in a
45.88 s transfer phase (`5.26e9`/s including interpolation and absorption).
The GEMM kernel runs at **`2.05e10` - `2.29e10` issued multiply-adds per
second per thread** (`2.208e10` at `N = 300` on 8 threads), that is
**3.6x - 4.0x** that rate.  Counting only the multiply-adds that are
structurally required, it still delivers `1.66e10`/s/thread at `N = 150` on
one thread and `1.83e10`/s/thread at `N = 300` on 8 threads,
**2.9x - 3.2x** the earlier engine's `5.7e9`.

Sustained `2.2e10` binary64 FMA multiply-adds per second per thread is
`1.1e10` `fmla .2d` instructions per second per thread; at the clock of
about 2.6 GHz of the laptop's CPU that is about 4.2 FMA issues per cycle,
essentially the full NEON FP issue width.  The kernel is compute bound.

### 8.5 Cost of a sweep

`B_300` has 1136 bits, so the reconstruction needs the 71 largest primes
below `2^16` or the 55 largest below `2^21` (`../harness/primes.py`); the
prime lists add 6 withheld primes to each.  Two concurrent 4-thread u16 jobs
would need 13.7 GB of the machine's 16 GiB and save only about 20 %, so a
sweep runs the primes one after another:

| build | per prime (8 threads) | peak RSS | primes | sweep |
|---|---|---|---|---|
| u16, `P < 2^16`, `R` in RAM | 198.98 s | 6.84 GB | 71 + 6 = 77 | 4.26 h |
| u32, `P < 2^21`, `--spill` | 225.16 s | 10.97 GB | 55 + 6 = 61 | 3.82 h |

The u16 sweep that produced `../../certificates/av12453_residues_300/` took
4 h 10 min.  Its binaries were compiled one per prime from the v1 source
with `g++ -O3 -march=native -std=c++17 -fopenmp -funroll-loops -DMODP=<p>ull`
and run by `../harness/run_all.sh --n 300 --threads 8 --extra-args "--prune"`.
For comparison, scaling the earlier engine's measured `N = 200` time
(154.04 s, 8 threads, `P = 65521`) by `(300/200)^6 = 11.4` gives about 29 min
per prime at `N = 300` (with 12.7 GiB by its own estimate), that is about
18 h for the 37 primes below `2^31` that it would need.

## 9. Verification of v1

**(a) `CERTIFY` at `N = 150`, both storage modes, two primes each, pruning on
and off**: 8/8 runs `CERTIFY: OK` for `0 <= n <= 150`, `support-check: OK`
everywhere, and `degree-check: OK` / `eval-check: OK` in the four unpruned
runs.

| build | `--prune` | wall (8 threads) | peak RSS | result |
|---|---|---|---|---|
| u16 `P=65521` | on / off | 4.71 s / 7.01 s | 419.9 / 426.6 MiB | OK / OK |
| u16 `P=65519` | on / off | 4.75 s / 6.57 s | 419.7 / 426.5 MiB | OK / OK |
| u32 `P=2097143` | on / off | 5.67 s / 7.70 s | 825.2 / 838.6 MiB | OK / OK |
| u32 `P=2097133` | on / off | 5.95 s / 8.05 s | 825.2 / 838.6 MiB | OK / OK |

The pruned and unpruned residue vectors are identical for all four primes
(151 terms each).

**(b) Full `R` tables.**  The `--dump-r` files of this engine and of the
earlier engine, built with the same `-DMODP=65521`, are byte-identical:

| `N` | table entries `RSIZE` | non-zero entries in the dump | result |
|---|---|---|---|
| 40 | 224 680 | 224 676 | identical (`cmp`) |
| 60 | 1 117 520 | 1 117 509 | identical (`cmp`) |

Both engines enumerate the same index set `l = 1..N`, `a = 0..N-l`,
`q = 0..N-l-a`, `s < slen(a,q)` and emit every non-zero entry, so byte
equality of the two dumps means that all 224 680 (resp. 1 117 520) table
entries agree.

The independent pure-Python reference `../pyref/ref.py`, written from the
printed equations of the paper (see `../pyref/README.md`), gives the same
tables: with its header line removed, the engine's dump is byte-identical to
the output of `ref.py N --mod P --dump-r FILE` at `N = 40` and `N = 60`, for
`P = 65521` (224 676 and 1 117 509 non-zero entries) and `P = 2097143`
(224 680 and 1 117 520).

In-binary `--engine both` (literal split, same storage) at `N = 40`:
`TABLE-MATCH: OK  all 224680 R entries agree`, for both u16 `P=65521` and
u32 `P=2097143`.

**(c) Agreement at scale.**  The earlier engine at `N = 200`, `P = 65521`,
8 threads, `--prune` (154.04 s, 2 639.4 MiB) and the u16 build of this engine
(23.53 s, 1 303.6 MiB): all 201 residues `n = 0..200` agree.

**(d) Prefix consistency.**  The residue vectors of the larger runs restrict
exactly to the smaller ones (0 mismatches): `N = 300` against `N = 200`
(201 terms) and `N = 200` against `N = 150` (151 terms), for both
`P = 65521` (u16) and `P = 2097143` (u32).

**(e) Spill path.**  `--spill` reproduces the in-RAM residues exactly at
`N = 60` (both storage modes) and at `N = 200` (`P = 2097143`, 201 terms),
and the spill file is exactly `RSIZE * sizeof(ST)` bytes (2 718 150 400 at
`N = 300`, u32).

**(f) Kernel and storage paths.**  The NEON and portable (`-DNO_NEON`) builds
agree, and so do the storage widths: `gemm_u32_65521` (u32 storage with a
16-bit prime) produces byte-identical `--dump-r` output to `gemm_u16_65521`.

---

## 10. Engine v2

v2 is v1 plus a parallel empty-stack phase, a hardened `CERTIFY`,
warning-clean flags and a tested `-DUSE_CBLAS` path.  `diff -u` of the two
sources has 193 lines in 9 hunks: the header comment, a CPU-time helper,
`terms()`, `load_truth_mod()` with the new `truth_required_entries()`, and
the checks and reporting in `main()`.  Every residue file and every
`--dump-r` file v2 produces is byte-identical to v1's (§10.7).

### 10.1 Parallel empty-stack phase

`Engine::terms()` evaluates the empty-stack recursion of the paper
(`eq:G`),

```
G[p][q] = sum_{h<p} G[h][mass-h-1]
        + sum_{h<q, delta=q-1-h}  ( delta == 0 ? G[p][h]
                                  : sum_{c<=p} sum_{s<slen(p-c,h)} R[delta][p-c][h][s] * G[c][s] )
```

over `mass = p+q = 1..N`.  In v1 this is one serial triple loop: at
`N = 300` it is 40 502 249 970 modular multiply-adds and 63.50 s of the
198.98 s eight-thread run (32 %), during which seven of the eight cores
idle.

The `mass+1` cells of one `mass` are mutually independent, so v2
parallelizes the loop over `p` with
`#pragma omp parallel for schedule(dynamic,1)` and a `reduction(+ : gm)` for
the instrumented counter.  The independence is exact (the argument is also
written into the source above `terms()`):

* `G[h][mass-h-1]` and the `delta == 0` term `G[p][h]` (with `p+h = mass-1`)
  are cells of mass `mass-1`;
* in the main term `c <= p`, `s < slen(p-c, h)` and `h <= q-1`, so
  `c+s <= c + slen(p-c,h) - 1`, which is `p+h <= mass-1` when `c = p`
  (`slen(0,h) = h+1`) and `p+h-1 <= mass-2` when `c < p`
  (`slen(a,h) = a+h`, `a >= 1`).

So every read is of a cell of strictly smaller mass, and the implicit
barrier at the end of each `mass` iteration orders the generations.  Each
cell keeps its own serial `u64` accumulation and `redP`/`partial` Barrett
folds in exactly the v1 order, so the arithmetic is untouched and the result
is bit-identical for every thread count (measured in §10.7, not assumed).

`schedule(dynamic,1)` is needed because the cost of cell `(p,q)` is about
`p*q*mass/2`, which varies by orders of magnitude across one `mass`.  The
heaviest single cell costs about `mass^3/8` of a total of about `mass^4/12`,
a fraction `1.5/mass`, so load imbalance stops mattering above `mass ~ 12`.

`-DNO_PARALLEL_EXTRACT` rebuilds the v1 serial loop with the v2
instrumentation; it exists only as the control for the timings of §10.8.

v1 printed one `extract` time that also contains `finalize_tables()`.  v2
adds, on stdout and in the `--sidecar` JSON,

```
# empty-stack phase: wall 0.792s  cpu 1.580s  (threads = 2, speed-up 2.00x)
# whole run: wall 11.241s  cpu 21.703s
```

with the JSON keys `empty_stack_wall_s`, `empty_stack_cpu_s` and
`total_cpu_s` (`extract_s` keeps its v1 meaning).  CPU time is
`clock_gettime(CLOCK_PROCESS_CPUTIME_ID)`, summed over all threads; it is the
figure to compare on a machine that also runs other jobs.

### 10.2 Hardened `CERTIFY`

v1 loads the truth file after the computation and then runs

```c
for (int n = 0; n <= N && n < (int)tr.size(); ++n) { ++nchecked; ... }
...
else printf("CERTIFY: OK  ... for 0 <= n <= %d\n", nchecked - 1);
```

so a truth file shorter than the run shrinks the check, and an empty truth
file makes it vacuous while the run still exits 0
(`CERTIFY: OK  a_n mod P matches the data file for 0 <= n <= -1`).  A run
that certifies only `n <= 99` still reports `OK`, and `run_all.sh` would
record it as a good prime.

v2:

* `truth_required_entries(N) = min(N,150) + 1`.  Fewer usable entries than
  that is a hard error with exit status 2, printing
  `CERTIFY: FAIL  truth file … supplies X entries, need Y (n = 0..Y-1)` on
  stdout and an explanation on stderr.  Exit status 2, distinct from the 1 of
  a failed check, is still a failure for `run_all.sh`, which records
  `FAIL … rc=2` and deletes the `.tmp` file.
* The truth file is loaded and length-checked before the engine is
  constructed, so a bad `--truth` fails in milliseconds instead of after the
  transfer.  Every run prints what it is going to check:
  `# truth file …/av12453_terms_0_150.txt: 151 entries, CERTIFY will check n = 0..150`.
* The parser also rejects a line with no degree field, a line with no value
  field, and a degree out of order (v1 only catches the last), each with the
  file name and line number.
* The default truth path is the same as in v1.

| binary | `--n` | `--truth` | exit status | stdout |
|---|---|---|---|---|
| v1 | 10 | empty file | **0** | `CERTIFY: OK … 0 <= n <= -1` |
| v1 | 10 | 100 entries | 0 | `CERTIFY: OK … 0 <= n <= 10` |
| v1 | 150 | 100 entries | **0** | `CERTIFY: OK … 0 <= n <= 99` |
| v2 | 10 | empty file | **2** | `CERTIFY: FAIL  … supplies 0 entries, need 11` |
| v2 | 10 | comments only | **2** | `CERTIFY: FAIL  … supplies 0 entries, need 11` |
| v2 | 150 | 100 entries | **2** | `CERTIFY: FAIL  … supplies 100 entries, need 151` |
| v2 | 150 | 101 entries | **2** | `CERTIFY: FAIL  … supplies 101 entries, need 151` |
| v2 | 10 | 100 entries | 0 | `CERTIFY: OK … 0 <= n <= 10` (11 >= 11 required) |
| v2 | 12 | 101 entries | 0 | `CERTIFY: OK … 0 <= n <= 12` |
| v2 | 10 | `0 1 / 1 1 / 2` | **2** | `truth file … line 3: no value field for n=2` |
| v2 | 10 | default path | 0 | `CERTIFY: OK … 0 <= n <= 10` |
| v2 | 10 | missing file | 2 | `cannot open /no/such/file` |
| v2 | 150 | default path | 0 | `CERTIFY: OK … 0 <= n <= 150` |

### 10.3 Warning-free build

`build.sh` and `build_primes.sh` compile with `-Wall -Wextra`
(`CXXFLAGS=-O3 -march=native -std=c++17 -fopenmp -funroll-loops -Wall -Wextra`,
`CFLAGS=-O3 -march=native -std=c11 -Wall -Wextra` for `cblas_stub/cblas_ref.c`).
g++ (Debian 14.2.0-19) 14.2.0 emits no diagnostics for any flavour:
`gemm_u16_65521`, `gemm_u16_65519`, `gemm_u32_2097143`, `gemm_u32_2097133`,
`gemm_u32_65521` (`-DSTORE_BITS=32`), `gemm_portable_65521` (`-DNO_NEON`),
`gemm_modp`, `gemm_cblas_65521` and `gemm_cblas_2097143` (`-DUSE_CBLAS`),
and the `-DNO_PARALLEL_EXTRACT` control builds.  The v1 source is also
clean under `-Wall -Wextra`.

### 10.4 The `-DUSE_CBLAS` path

`cblas_stub/cblas.h` declares the two CBLAS enums and `cblas_dgemm` with the
reference (Netlib / OpenBLAS / Accelerate) signature and nothing else, so a
source that compiles against it also compiles against a real CBLAS.
`cblas_stub/cblas_ref.c` implements it as a naive `i-k-j` triple loop in
C11.  It supports exactly the one call the engine makes,

```c
cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans,
            MPb, nsPad, K, 1.0, Ap, K, Bp, nsPad, 1.0, C, nsPad);
```

and calls `abort()` with a diagnostic on any other order, transpose,
`alpha`, `beta` or inconsistent leading dimension, so it cannot silently
cover up a wrongly issued call.  It is a correctness reference only and says
nothing about the speed of a real BLAS.  A different summation order gives
the same bits for the reason given in §3.

The build (`build.sh` does the same):

```bash
gcc -O3 -march=native -std=c11 -Wall -Wextra -c cblas_stub/cblas_ref.c -o tmp/cblas_ref.o
g++ -O3 -march=native -std=c++17 -fopenmp -funroll-loops -Wall -Wextra \
    -DMODP=65521ull -DUSE_CBLAS -Icblas_stub av12453_gemm_split_v2.cpp \
    tmp/cblas_ref.o -o bin/gemm_cblas_65521
```

With `--threads 1 --prune`, against the built-in micro-kernel of the same
prime:

| prime | `N` | residues | `--dump-r` | `reduce_ops` micro-kernel / CBLAS | `split_madds_issued` micro-kernel / CBLAS | split time |
|---|---|---|---|---|---|---|
| 65521 | 60 | **byte-identical** | **byte-identical** | 1 618 432 / 1 618 432 | 1 670 940 544 / 1 670 940 544 | 0.111 s / 0.333 s |
| 65521 | 100 | **byte-identical** | **byte-identical** | 12 495 392 / 12 495 392 | 29 902 907 808 / 35 379 881 888 | 1.695 s / 6.626 s |
| 2097143 | 60 | **byte-identical** | **byte-identical** | 1 618 432 / 1 618 432 | 1 670 940 544 / 1 670 940 544 | 0.101 s / 0.354 s |
| 2097143 | 100 | **byte-identical** | **byte-identical** | 27 198 432 / 27 198 432 | 29 902 907 808 / 35 379 881 888 | 1.775 s / 7.555 s |

Both builds also pass `selftest`, `support-check` and `CERTIFY` in every
run, and the CBLAS build passes the in-binary literal-split comparison
(`--engine both`, `N = 40`).

The CBLAS path uses the same `PRODLIMIT` reduction schedule.  The schedule
lives in the `(w, j, tau1)` driver loop, outside the `#ifdef USE_CBLAS`:

```c
if (pc + (u64)K > PRODLIMIT) { reduce_block(C, MP*nsPad); rd += MP*nsPad; pc = 1; }
pc += (u64)K;
```

`K = tau1`, `MP` and `nsPad` do not depend on the kernel, so the reductions
happen at identical `(w, j, tau1)` and cover identical buffers.  The
`reduce_ops` counter confirms it: it is equal for the two builds at every
`(prime, N)` tested, including `27 198 432` for `P = 2097143` at `N = 100`,
where the `PRODLIMIT = 2048` schedule fires many intermediate reductions,
against `12 495 392` for `P = 65521`, where only the final reduction per
`(W,j)` runs.  The bound also stays valid for CBLAS: the accounting charges
`K` products per block per `C` entry, which is the maximum, whereas the
blocked kernel issues only `K - mstart` for the entries of a block whose
first rows the staircase skips; CBLAS issues the full `K`, inside the same
budget.

`split_madds_issued` is the one counter that legitimately differs, and only
where the staircase matters: at `N = 60` every `ns = w-2 <= 58` fits in one
`NCB = 64` column block with `mstart = 0`, so the two kernels issue exactly
the same FMAs; at `N = 100` the second column block has `mstart > 0`, and the
CBLAS path, which drops the staircase blocking, issues
`35 379 881 888 / 29 902 907 808 = 1.183x` as many.  The naive reference is
3.0x - 4.3x slower in split time than the built-in NEON micro-kernel, as
expected of a triple loop.

Whether Accelerate or OpenBLAS beats the built-in kernel has to be measured
on the machine in question, and the handicap grows with `N`.  An enumeration
of the loop nests of the two kernels, which reproduces the measured
`split_madds_issued` exactly, gives:

| `N` | blocked issued | CBLAS issued | CBLAS / blocked |
|---|---|---|---|
| 60 | 1 670 940 544 | 1 670 940 544 | 1.000 |
| 100 | 29 902 907 808 | 35 379 881 888 | 1.183 |
| 150 | 325 738 808 704 | 400 718 307 712 | 1.230 |
| 200 | 1 752 053 397 536 | 2 243 333 132 320 | 1.280 |
| 300 | 18 819 551 098 976 | 25 473 600 960 608 | **1.354** |

So at `N = 300` a BLAS must be more than **1.354x** faster than the
built-in kernel just to break even, and on the machine of §8 the built-in
kernel already sustains about `2.2e10` multiply-adds per second per thread,
essentially the full NEON FP issue width.  The `--cblas accelerate` and
`--cblas openblas` recipes of `build_primes.sh` have not been tested; only
`--cblas stub` has been compiled and run.

### 10.5 `build_primes.sh`

The modulus is a compile-time constant, so a CRT sweep needs one binary per
prime.  `build_primes.sh` builds them all in parallel and names them exactly
as the default `--pattern` of `../harness/run_all.sh` expects
(`<outdir>/av12453_gemm_<prime>`).  It changes into this directory first, so
relative `--primes`, `--outdir` and `--src` paths are taken relative to
`engine/`.

```
./build_primes.sh --primes FILE [--outdir DIR] [--jobs K] [--store 16|32]
                  [--cblas none|accelerate|openblas|stub] [--src FILE]
                  [--cxx CXX] [--extra "flags"] [--dry-run] [--check-primality]
```

* **Linux / g++** (auto-detected): `-O3 -march=native -std=c++17
  -funroll-loops -Wall -Wextra -fopenmp`.
* **macOS / Apple clang**: `-march=native` is probed first, then
  `-mcpu=native`, then `-mcpu=apple-m1`.  Apple clang has no OpenMP, so the
  script looks for Homebrew `libomp` via `brew --prefix libomp` and, if found,
  uses `-Xpreprocessor -fopenmp -I<prefix>/include` and
  `-L<prefix>/lib -lomp`.  Without `libomp` it warns and builds
  single-threaded binaries instead of failing.
* **macOS / Homebrew g++**: `--cxx g++-14`, and it behaves like the Linux
  case.
* `--cblas accelerate` adds `-DUSE_CBLAS -DACCELERATE_NEW_LAPACK` with the
  vecLib headers from `xcrun --show-sdk-path` and `-framework Accelerate`;
  `--cblas openblas` finds `cblas.h` in the usual places and links
  `-lopenblas`; `--cblas stub` builds against `cblas_stub/` (correctness
  only).
* `--check-primality` trial-divides every modulus and refuses any
  `p >= 2^21`, which the exactness argument does not cover.
* `--dry-run` prints the compile commands and stops.
* After building it runs one smoke test of the first binary
  (`--n 30 --threads 1`) and exits non-zero if any binary failed to build or
  the smoke test failed.

It was tested on a three-prime list (65521, 65519, 2097143) with
`--jobs 2`: all three binaries built, `run_all.sh --dry-run` resolved
`<outdir>/av12453_gemm_<prime>` for all three, an `N = 60` sweep gave
`SUMMARY ok=3 skip=0 fail=0`, and an immediate re-run gave
`SUMMARY ok=0 skip=3 fail=0` (the resume path).  `RUN_ON_LAPTOP.md` describes
the whole pipeline; with v2 binaries from `build_primes.sh` it has been run
end to end only at `N = 60`, while the `N = 300` sweep used the v1 binaries
of §8.5.

### 10.6 What v2 leaves unchanged

* The split kernel, the micro-kernel, the packing, the pruning, the
  interpolation, the bands and `D` term, the absorption, the spill path and
  all arithmetic are the v1 code, byte for byte.
* The residue-file header still reads
  `# engine av12453_gemm_split storage <s> threads <k> prune <0|1>` (not
  `_v2`), so that v2's output files are byte-identical to v1's and a sweep
  can be finished with a mixture of both.  The engine name in the stdout
  banner is unchanged as well; a v2 run is recognized by the extra
  `# truth file …` and `# empty-stack phase: …` lines.
* `--dump-r`, `--sidecar` (which gains three keys and loses none), `--spill`,
  `--engine naive|both`, `--prune`, the rest of the command line and the
  exit-status contract are unchanged; `../harness/run_all.sh` and
  `../harness/reconstruct.py` work with either version.
* The exactness argument, `PRODLIMIT`, `selftest`, `support-check`,
  `degree-check`, `eval-check` and `TABLE-MATCH` are unchanged and all pass.

### 10.7 Verification of v2

* **Byte identity with v1.**  For the builds `gemm_u16_65521` and
  `gemm_u32_2097143`, `N = 100` and `150`, and 1 and 2 threads (8 pairs), the
  residue files and the `--dump-r` files of v1 and v2 are byte-identical.
  At `N = 300` (`P = 65521`, 8 threads) v2 reproduces the residue file of
  the sweep.
* **Counters.**  The unpruned `N = 150` runs (`--threads 2`) of v1 and v2
  agree exactly (structural `446 984 370 494`, issued `623 043 607 808`;
  §8.2), produce byte-identical residue files and pass `CERTIFY` for
  `0 <= n <= 150`, `degree-check` and `eval-check`.  The `empty-stack madds`
  counter is `1 265 906 235` at `N = 150` in every run of §10.8, serial or
  parallel.
* **`CERTIFY`**: the 13 cases of §10.2.
* **CBLAS**: §10.4.
* **Packaging**: §10.5.
* **Cross-checks of v1, repeated on the v2 binaries:**

| check | result |
|---|---|
| `--engine both` (literal split), `N = 40`, CBLAS build | `TABLE-MATCH: OK  all 224680 R entries agree`, `CERTIFY: OK` |
| `R` table `N = 60`: `gemm_u16_65521` against `gemm_portable_65521` (`-DNO_NEON`) | byte-identical |
| `R` table `N = 60`: `gemm_u16_65521` against `gemm_u32_65521` (`-DSTORE_BITS=32`) | byte-identical |
| `R` table `N = 60`: `gemm_u16_65521` against `gemm_cblas_65521` (`-DUSE_CBLAS`) | byte-identical |
| `--spill` against in-RAM residues, `N = 60`, `P = 2097143` | identical; spill file 4 470 080 B = `RSIZE * 4` |
| `selftest`, `support-check`, `CERTIFY` | OK in all 53 runs (no `FAIL`, no `VIOLATION`) |
| `degree-check`, `eval-check` (unpruned runs) | OK |

The byte identity with v1 is checked with commands of this form, run from
the repository root so that the default `--truth` path resolves:

```bash
g++ -O3 -march=native -std=c++17 -fopenmp -funroll-loops -DMODP=65521ull \
    code/av12453_n300/engine/av12453_gemm_split_v1.cpp -o v1_65521
g++ -O3 -march=native -std=c++17 -fopenmp -funroll-loops -DMODP=65521ull \
    code/av12453_n300/engine/av12453_gemm_split_v2.cpp -o v2_65521
./v1_65521 --n 150 --threads 2 --prune --out v1.res --dump-r v1.dump
./v2_65521 --n 150 --threads 2 --prune --out v2.res --dump-r v2.dump
cmp v1.res v2.res && cmp v1.dump v2.dump
```

### 10.8 Measurements of v2

**Empty-stack phase at `N = 150`**, `--prune`, measured while the
`N = 300` sweep occupied 8 of the machine's 9 CPUs.  `SER` is
`-DNO_PARALLEL_EXTRACT` (the v1 serial loop with the v2 timers), `PAR` the
v2 loop.  Two repetitions each; both are shown because the spread of the
wall times comes from the other load.

| prime | build | threads | wall (s), 2 reps | **CPU (s), 2 reps** |
|---|---|---|---|---|
| 65521 (`u16`) | SER | 1 | 1.669, 1.631 | **1.472, 1.630** |
| 65521 (`u16`) | PAR | 1 | 1.817, 1.652 | **1.596, 1.646** |
| 65521 (`u16`) | SER | 2 | 1.821, 1.539 | **1.590, 1.537** |
| 65521 (`u16`) | PAR | 2 | 1.678, **0.822** | **1.585, 1.643** |
| 2097143 (`u32`) | SER | 1 | 2.536, 2.520 | **2.249, 2.219** |
| 2097143 (`u32`) | PAR | 1 | 2.599, 2.432 | **2.299, 2.431** |
| 2097143 (`u32`) | SER | 2 | 2.517, 2.357 | **2.239, 2.356** |
| 2097143 (`u32`) | PAR | 2 | 1.899, **1.261** | **2.418, 2.509** |

In the `N = 150` byte-identity runs of §10.7, which print the same timer:

| prime | v1 `extract` wall | v2 `empty-stack` wall | v2 `empty-stack` CPU |
|---|---|---|---|
| 65521, 1 thread | 1.668 s | 1.647 s | 1.440 s |
| 65521, 2 threads | 1.678 s | **0.792 s** | 1.580 s |
| 2097143, 1 thread | 2.430 s | 2.351 s | 2.105 s |
| 2097143, 2 threads | 2.409 s | **1.240 s** | 2.472 s |

* **CPU time is essentially unchanged**: serial 1.472-1.630 s against
  parallel 1.440-1.646 s (`u16`), 2.219-2.356 s against 2.105-2.509 s
  (`u32`).  The parallel-for construct costs at most a few per cent, inside
  the ±10 % run-to-run spread under this load.  The work itself is
  identical: the `empty-stack madds` counter is `1 265 906 235` in all 16
  runs.
* **Wall time halves when two CPUs are free.**  Best 2-thread wall `0.822 s`
  against the best serial `1.539 s` (`u16`) = **1.87x**; `1.261 s` against
  `2.357 s` (`u32`) = **1.87x**.  Against the v1 binary's own `extract` in
  the identity runs, `1.678 -> 0.792` = **2.12x** and `2.409 -> 1.240` =
  **1.94x**; the CPU/wall ratio there is `1.580/0.792 = 2.00` and
  `2.472/1.240 = 1.99`, so both threads ran.
* **On a saturated machine there is no wall-clock gain**: the first `PAR`,
  2-thread repetitions (`1.678 s`, `1.899 s`) ran while the sweep held all
  8 CPUs, with CPU/wall ratios `0.94` and `1.27`.  The same binary and phase
  took `0.822 s` and `1.678 s` of wall time in two runs minutes apart, which
  is why CPU time is the figure to compare.

**`N = 300`** (`P = 65521`, 8 threads, measured on the idle machine after the
sweep; `../../../notes/av12453_300_computation_report.md`): 150.0 s wall
instead of v1's 198.98 s, with the empty-stack phase taking 10.4 s instead
of 63.5 s; the residue file is identical to the one of the sweep.  A sweep of
77 primes with v2 would take about 3.2 hours on that machine.
