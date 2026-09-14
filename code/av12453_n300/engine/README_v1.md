# `av12453_gemm_split` — GEMM realization of the homogeneous split scheme

Directory: `code/av12453_n300/engine/` (developed in a scratch working directory; the files are kept here)

| file | what it is |
|---|---|
| `av12453_gemm_split.cpp` | the engine (single source, 968 lines) |
| `build.sh` | builds every flavour into `bin/`, verifying primality of each hard-wired modulus |
| `rusage_run.c` | `fork`/`wait4` stand-in for `/usr/bin/time` (absent on this container) |
| `pack_residues.py` | converts the per-prime residue files into the `# modulus P` bundle that `repo/code/reconstruct_av12453_rns.py` reads |
| `old_homog_split_out.cpp` | byte-for-byte copy of `repo/code/av12453_homog_split.cpp` **plus** an `--out FILE` flag that prints its `terms()` (13 added lines, `diff` in §7); used only as the cross-engine reference |
| `out/` | residue files + JSON sidecars |
| `logs/` | raw run logs (`*.log`) and `rusage_run` output (`*.rusage`) |

Started from `repo/code/av12453_homog_split.cpp`. Everything that is not the split
kernel is kept: the BAND1/BAND2/D terms, the inverse-Vandermonde interpolation,
absorption of the finished grade into `E`, the empty-stack phase (`terms()`), the
`CERTIFY` check against `repo/code/data/av12453_terms_0_150.txt`, the support check
of interpolated values, `--dump-r`, the literal-split reference engine
(`--engine naive|both`) and the instrumented counters.

---

## 1. The recurrence and what is being replaced

```
R[l][a][q][s] = sum_{h<a} R[l][h][a+q-h-1][s]                    (BAND1)
              + sum_{r<q} R[l+q-r-1][a][r][s]                    (BAND2)
              + (l==1 ? [a==0 && q==s] : 2 R[l-1][a][q][s])      (D)
              + SPLIT[l][a][q][s]
SPLIT[l][a][q][s] = sum_{l1+l2=l-1} sum_{a1+a2=a} sum_m R[l1][a1][q][m] R[l2][a2][m][s]
```
with `l >= 1`, `a,q >= 0`, `l+a+q <= N`, `s < slen(a,q) = (a==0 ? q+1 : a+q)`.

With the offset grade `t = l+a` and the slice polynomials
`C_t(y;u,v) = sum_{a<t} y^a R[t-a][a][u][v]` (stored evaluated at `y = y_j` as
`E[j][t][u][v]`, row length `scount(t,u) = (t==1 ? u+1 : t+u-1)`), homogeneity gives,
for output grade `W` and every point `y_j`,

```
Phi_W(y_j;q,s) = sum_{tau1=1}^{W-2} sum_m E[tau1-q][q][m] * E[W-1-tau1][m][s]
               = sum_a y_j^a SPLIT[W-q-a][a][q][s].
```

The old engine evaluated that double sum with an `axpy` over one scalar at a time and
one Barrett fold per product. The new engine evaluates it as a **dense matrix product
with no modular reduction inside**.

## 2. The GEMM formulation

Fix a grade `W` and a point `j`. For every `g2 = 1 .. W-2` put `tau1 = W-1-g2` and

* `A` = `tau1 x tau1`, `A[q][m] = C_{tau1-q}(y_j;q,m)`, `q = 0..tau1-1` — all slices of
  grade `tau1`. Row `q` carries `scount(tau1-q,q)` entries, i.e. `tau1-1` for
  `q < tau1-1` and `tau1` for `q = tau1-1`; the rest is zero padding.
* `B` = `tau1 x (W-2)`, `B[m][s] = C_{g2}(y_j;m,s)` — an **upper staircase**: row `m`
  carries `scount(g2,m)` entries, so row lengths grow by one per row.

Then `Phi_W(y_j) = sum_{g2} A·B`, accumulated into one `(W-2) x (W-2)` buffer `C`.

Three exact reductions of the work:

1. **Row pruning.** `SPLIT[l][...] = 0` for `l < 3` (the split needs `l1,l2 >= 1`), so
   `deg_y Phi_W(·;q,·) <= W-q-3` and coordinate `q` needs exactly the `W-q-2` points
   `y = 1..W-q-2`. Equivalently: the 1-based point `y = j` is needed only for the rows
   `q <= W-2-j` of `A`. The engine therefore evaluates `M = min(tau1, W-2-j)` rows and
   interpolates coordinate `q` from `W-q-2` points. (This is two points sharper than
   `av12453_homog_split --prune`, which uses `W-q` points. Both are exact; the two
   engines' structural madd counts therefore differ by ~2 %.)
2. **Staircase column blocks.** `B` is packed one `NC = 64`-wide column block at a time,
   and each block starts at the first row that reaches it,
   `mstart(s0) = (g2 == 1 ? s0 : max(0, s0+2-g2))`. Only the `NR`-wide tail of a block
   wastes multiplications, so the padding overhead is `O(NR)` per row instead of
   `O(tau1)`.
3. **Zero-row padding** of `A` up to a multiple of `MR = 4` (at most 3 wasted rows).

Measured cost of the packing: at `N = 300` the engine issues `1.882e13` FMA
multiply-adds against a structural requirement of `1.5623e13`, i.e. a factor **1.205**
(the brief's estimate for the unblocked version was 1.6).

### Micro-kernel

`MR x NR = 4 x 8` accumulators in 16 NEON `float64x2_t` registers, `K`-loop over `m`
with four `fmla vD.2d, vB.2d, vA.d[0]`-style scalar-broadcast FMAs per accumulator row
(`vfmaq_n_f64`). `A` is packed row-major (`MR` rows of `K` doubles), `B` block-packed
`(K-mstart) x ncPad`. Build `-DNO_NEON` for the portable version of the same 4x8 kernel;
gcc 14.2 `-O3 -march=native` auto-vectorizes it to within 1.5 % of the intrinsics
(`N = 150`, 8 threads: 4.075 s vs 4.044 s, 21.74 vs 22.06 Gmadd/s/thread). Build `-DUSE_CBLAS` to replace the
blocked kernel by one `cblas_dgemm` per `(j,g2)` on the same packed double panels
(this path drops the staircase blocking and does the full `MPb x nsPad x K` product).

## 3. Exactness of each build

Storage width is a compile-time choice, defaulting to `u16` for `P < 2^16` and `u32`
otherwise (`-DSTORE_BITS=16|32` overrides). Everything that enters the GEMM is a
residue in `[0,P)`, and the accumulator is IEEE binary64, in which **every integer
below `2^53` is exact** and integer `+`, `*` on such values are exact.

Let `PRODLIMIT = floor(2^53 / (P-1)^2)` — the number of products that can be summed
before the accumulator can leave the exact range. The engine tracks, for every `C`
entry, an upper bound on the number of products accumulated since the last reduction
(the sum of the inner dimensions `tau1` of the `g2` blocks done so far) and reduces `C`
modulo `P` whenever the next block could push it past `PRODLIMIT`. Each reduction
leaves values `< P`, which is charged as one product.

| build | `P` | storage | `(P-1)^2` | `PRODLIMIT` | products actually needed per `C` entry, `N = 300` | reductions per `(W,j)` |
|---|---|---|---|---|---|---|
| `gemm_u16_65521` | 65521 | `u16` | `< 2^32` | 2 098 176 | `sum_{tau1<W} tau1 <= 44 551` | 1 (only the final one) |
| `gemm_u16_65519` | 65519 | `u16` | `< 2^32` | 2 098 304 | same | 1 |
| `gemm_u32_2097143` | 2097143 | `u32` | `< 2^42` | 2 048 | same | `~W^2/(2·2048)`, ≤ 22 at `W = 300` |
| `gemm_u32_2097133` | 2097133 | `u32` | `< 2^42` | 2 048 | same | ≤ 22 |

So for the two 16-bit primes the whole grade accumulates without a single reduction
(`44 551 · 2^32 < 2^48.5 < 2^53`), and for the two 21-bit primes the periodic reduction
keeps the accumulator below `2048 · 2^42 = 2^53`. Both bounds are *static*: the
`static_assert(PRODLIMIT >= 64)` and the runtime counter are what enforce them, so a
different `-DMODP` is safe automatically as long as `P < 2^21`.

The reduction of an exact non-negative integral double `x < 2^53` uses
`r = x - P·floor(x·(1/P))` followed by two conditional corrections; `floor(x·(1/P))`
differs from `floor(x/P)` by at most 1 because the relative error of the product is
`<= 2^-52` and `2^53/P · 2^-52 < 1`. The binary is **self-testing**: every run compares
this reduction with integer `%` on 200 000 random values `< 2^53` plus the boundary
values and exits non-zero on any disagreement (`selftest: OK` line).

The `--dump-r`, interpolation, band, absorption and empty-stack code paths stay in
64-bit Barrett integer arithmetic exactly as in the old engine.

`-DUSE_CBLAS` keeps the same bounds: `cblas_dgemm(..., beta = 1.0)` accumulates into
the same `C` in binary64, and the driver still reduces on the same `PRODLIMIT`
schedule, so the CBLAS path is exact under exactly the argument above.

## 4. Memory model

`E` (the evaluated slice table) dominates. Sizes below are exact counts, not estimates.

```
ESIZE  = sum_{t=1..N} sum_{u=0..N-t} scount(t,u)
points = N-2 with pruning (the 1-based point j is never used above grade j+2),
         N+1 without
RSIZE  = sum_{w=1..N} [ w(w+1)/2 + (w-1)w(2w-1)/6 ]
```

| `N` | `ESIZE` | points | `E` entries | `E` u16 | `E` u32 | `RSIZE` | `R` u16 | `R` u32 |
|---|---|---|---|---|---|---|---|---|
| 150 | 1 125 100 | 148 | 166 514 800 | 333 MB | 666 MB | 42 759 425 | 86 MB | 171 MB |
| 200 | 2 666 800 | 198 | 528 026 400 | 1.06 GB | 2.11 GB | 134 683 400 | 269 MB | 539 MB |
| **300** | **9 000 200** | **298** | **2 682 059 600** | **5.364 GB** | **10.728 GB** | **679 537 600** | **1.359 GB** | **2.718 GB** |

(The brief's `2 709 060 200` is the same table with all `N+1 = 301` points; the two
points that pruning removes save 27 000 600 entries.)

Everything else at `N = 300`: inverse Vandermonde `sum_{n<=298} n^2 = 8 865 649`
`u32` = **35.5 MB**; the per-grade evaluated buffer `Cbuf`
`298·298·298 = 26 463 592` entries = **52.9 MB** (`u16`) / **105.9 MB** (`u32`);
per-thread GEMM scratch (`A`, `B`, `C` double panels) `< 2.5 MB` x 8 threads =
**20 MB**; the `G` table of the empty-stack phase `301^2` `u32` = 0.4 MB.

`R` is **not** needed in full during the transfer: `bands(w)` reads only grade `w-1`,
and `split`/`absorb` only grade `w`. Two rolling grade buffers therefore suffice
(`max_w GS(w) = 9 000 200` entries at `N = 300`, i.e. **18 MB** `u16` / **36 MB**
`u32`). With `--spill` the engine keeps exactly those two buffers, appends each
finished grade to a file, then — before the empty-stack phase, which does need all
grades — frees `E`, `Wpre` and `Cbuf` and reads the file back into one contiguous `R`.

Resulting peaks at `N = 300` (measured, `--prune`, 8 threads):

| build | mode | predicted peak | measured peak RSS |
|---|---|---|---|
| `u16`, `P = 65521` | `R` in RAM | `5.364 + 1.359 + 0.09` = 6.81 GB | **6 521.6 MiB = 6.84 GB** |
| `u32`, `P = 2097143` | `--spill` | transfer `10.728 + 0.036 + 0.14` = 10.90 GB; extraction `2.718` GB | **10 460.2 MiB = 10.97 GB** |
| `u32`, `P = 2097143` | `R` in RAM (not run at `N=300`) | `10.728 + 2.718 + 0.14` = 13.59 GB | — |

Without `--spill` the `u32` build at `N = 300` would need `10.728 + 2.718 = 13.4 GB`,
which is why the spill path exists.

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
Header lines start with `#`; the body is `n residue` for `n = 0..N`, consecutive.
`repo/code/reconstruct_av12453_rns.py --independent-residue P:PATH` reads this
directly (it skips `#` lines). `./pack_residues.py FILES... -o bundle.txt` converts a
set of them into the `# modulus P` packed bundle that the same script's positional
argument expects.

**Sidecar** (`--sidecar FILE`): one JSON object with `prime`, `storage`, `N`,
`threads`, `prune`, `spill`, `wall_s`, `transfer_s`, `split_s`, `interp_s`,
`absorb_s`, `bands_s`, `extract_s`, `peak_rss_kib`, all instrumented counters
(`split_madds_structural`, `split_madds_issued`, `pack_a`, `pack_b`, `reduce_ops`,
`interp_madds`, `absorb_madds`, `empty_stack_madds`, `band_adds`),
`gemm_madds_per_s_total`, `gemm_madds_per_s_per_thread`, `E_entries`, `R_entries`,
`residue_fnv1a64` (FNV-1a of the residue vector), `certify`, `certify_upto`,
`exit_code`.

**R dump** (`--dump-r FILE`): `# P <prime> N <N>` then one line `l a q s value` per
non-zero entry, in the order `l = 1..N`, `a = 0..N-l`, `q = 0..N-l-a`, `s = 0..slen-1`.
Byte-identical to `av12453_homog_split --dump-r`.

**Spill file** (`--spill-file FILE`): raw `ST` (`uint16_t`/`uint32_t`) grade blocks
appended in grade order, grade `w` occupying `GS(w) = w(w+1)/2 + (w-1)w(2w-1)/6`
entries, each grade laid out by `l = 1..w` then `a = 0..w-l`, row length `slen(a,w-l-a)`.
It is exactly the concatenation of the in-RAM `R`, so read-back is one `fread`.

**Exit status.** Non-zero if any of: the binary64-reduction self-test, the support
check, the degree check, the evaluation-consistency check, `CERTIFY`, or the
`--engine both` table match fails.

## 6. Built-in checks

| check | when | what it asserts |
|---|---|---|
| `selftest` | every run | the binary64 `mod P` used inside the GEMM equals integer `%` on 2·10^5 random values `< 2^53` and on the boundary values |
| `support-check` | every `--engine gemm` run | no interpolated split value lands outside `s < slen(a,q)` |
| `degree-check` | unpruned runs | no interpolated `y^a` coefficient with `a > W-q-3` is non-zero (this is the fact that makes the row pruning exact) |
| `eval-check` | unpruned runs | the two evaluation points *not* used by the interpolation reproduce the interpolant by Horner — an independent test of the homogeneity identity |
| `CERTIFY` | every run | `a_n mod P` equals `repo/code/data/av12453_terms_0_150.txt` for `n <= min(N,150)` |
| `TABLE-MATCH` | `--engine both` | the full `R` table equals the literal-split engine in the same binary |

## 7. Command line

```
av12453_gemm_split --n N [--engine gemm|naive|both] [--threads K] [--prune]
                   [--spill [--spill-file F]] [--dump-r FILE]
                   [--out RESIDUES] [--sidecar FILE] [--truth FILE]
```
`--prune` turns on the sharp degree pruning (recommended; `N-2` evaluation points).
Without it every one of the `N+1` points is evaluated for every coordinate and the two
extra structural checks above are run. `--spill` is incompatible with `--dump-r` and
with `--engine naive|both` (both need the whole table in RAM).

## 8. Measurements

Machine: aarch64 container, 9 visible CPUs (8-CPU quota), 17 GB RAM, g++ 14.2.0,
`-O3 -march=native -std=c++17 -fopenmp -funroll-loops`. Times are wall clock from
`bin/rusage_run`; peak RSS is the child's `ru_maxrss` from `wait4` (`/usr/bin/time` is
not installed on this container). All runs use `--prune` unless stated.

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

The `extract` column is the empty-stack phase, which is still serial; it is 32 % of the
`N = 300` u16 run and is the obvious next thing to parallelize.

### 8.2 Instrumented multiply-adds

`structural` counts the multiply-adds the split *must* do (identical definition to the
old engine's `split madds structural`); `issued` counts the FMA slots the GEMM actually
executes, including staircase and `MR`-padding.

| `N` | structural | issued | issued/structural | structural / `(N^6/24)` |
|---|---|---|---|---|
| 100 | 19 924 528 568 | 29 902 907 808 | 1.501 | 0.478 |
| 150 | 235 381 173 728 | 325 738 808 704 | 1.384 | 0.496 |
| 200 | 1 346 818 281 138 | 1 752 053 397 536 | 1.301 | 0.505 |
| 300 | 15 622 561 507 708 | 18 819 551 098 976 | 1.205 | 0.514 |

Unpruned (`N = 150`): structural `446 984 370 494`, issued `623 043 607 808`. So the
degree pruning removes 47 % of the work, and the GEMM padding overhead falls from 1.50
at `N = 100` to 1.20 at `N = 300` (it is `O(NR/tau1)` per row block).

Other counters at `N = 300`: `pack A` 101 073 438 600 and `pack B` 184 762 592 672
element conversions (1.5 % of the FMA count), `interp` 158 982 693 805 modular
multiply-adds, `absorb` 202 502 204 800, empty-stack 40 502 249 970, band adds
2 011 612 200. The `u16` build performs 1 012 456 192 binary64 reductions of `C`
(one pass per `(W,j)`); the `u32` build performs 15 984 316 864 (the `PRODLIMIT = 2048`
schedule), which is 0.085 multiplications' worth per issued FMA and explains most of
the `u16`/`u32` gap.

### 8.3 Thread scaling (`N = 150`, u16 `P = 65521`, `--prune`)

| threads | wall (s) | split (s) | Gmadd/s (all) | Gmadd/s/thread | speed-up (wall) |
|---|---|---|---|---|---|
| 1 | 21.89 | 14.22 | 22.91 | 22.91 | 1.00 |
| 2 | 11.73 | 7.21 | 45.17 | 22.59 | 1.87 |
| 4 | 6.80 | 3.69 | 88.22 | 22.05 | 3.22 |
| 8 | 4.13 | 1.89 | 172.8 | 21.59 | 5.30 |

The GEMM phase itself scales 7.52x on 8 threads; the whole-run 5.30x is limited by the
serial empty-stack phase (1.2-1.3 s at `N = 150`).

### 8.4 Comparison with `av12453_homog_split`

Same box, same flags, `--prune`, `--engine saprime`:

| run | old engine | new engine | ratio |
|---|---|---|---|
| `N = 150`, 1 thread, `P = 2^31-1` (its fastest modulus, Mersenne fold) | **47.48 s**, 844.7 MiB | 21.89 s, 414.0 MiB (u16) / 23.92 s, 819.4 MiB (u32) | **2.17x** faster, 2.0x less RAM |
| `N = 150`, 1 thread, `P = 65521` (same prime, Barrett) | **172.98 s**, 844.7 MiB | 21.89 s, 414.0 MiB | **7.90x** |
| `N = 200`, 8 threads, `P = 65521` (same prime) | **154.04 s**, 2 639.4 MiB | 23.53 s, 1 303.6 MiB | **6.55x**, 2.0x less RAM |

**Kernel throughput.** The old engine's split rate is quoted in the brief as
`5.7e9` multiply-adds per second per thread; reproduced here it executed
`2.413e11` split multiply-adds inside a 45.88 s transfer phase
(`5.26e9`/s including interpolation and absorption). The new GEMM kernel runs at
**`2.05e10` - `2.29e10` issued multiply-adds per second per thread**
(`2.208e10` at `N = 300` on 8 threads), i.e. **3.6x - 4.0x** the old rate. Counting only
the multiply-adds that are structurally required, the new engine still delivers
`1.66e10`/s/thread at `N = 150` on one thread and `1.83e10`/s/thread at `N = 300`
on 8 threads, **2.9x - 3.2x** the old engine's `5.7e9`.

Sustained `2.2e10` binary64 FMA madds/s/thread is 1.1e10 `fmla .2d`
instructions/s/thread; at the ~2.6 GHz of this part that is about 4.2 FMA issues per
cycle, i.e. essentially the full NEON FP issue width. The kernel is compute bound.

### 8.5 Extrapolation to the full `N = 300` prime set

`B_300` needs 1136 bits, so ~72 primes below `2^16` or ~55 below `2^21`
(plus a few withheld for the redundancy check).

| plan | per prime (8 threads) | peak RSS | 72 / 55 primes | with 5 redundant |
|---|---|---|---|---|
| u16, `P < 2^16`, `R` in RAM | 198.98 s | 6.84 GB | **3.98 h** | 4.26 h (77) |
| u32, `P < 2^21`, `--spill` | 225.16 s | 10.97 GB | **3.44 h** | 3.75 h (60) |

Only one job fits at a time (two concurrent 4-thread u16 jobs would need 13.7 GB and
save only ~20 %), so these are sequential wall-clock totals. For comparison, the old
engine extrapolates from its measured `N = 200`, 8-thread, `P = 65521` time by
`(300/200)^6 = 11.4x` to ~29 min per prime at 12.7 GiB, i.e. ~18 h for its 37
31-bit primes even before the Mersenne/Barrett penalty is taken into account.

## 9. Verification performed

All commands and raw output are in `logs/`.

**(a) `CERTIFY` at `N = 150`, both storage modes, two primes each, pruning on and off**
— 8/8 runs `CERTIFY: OK` for `0 <= n <= 150`, plus `support-check: OK` everywhere and
`degree-check: OK` / `eval-check: OK` in the four unpruned runs.

| build | `--prune` | wall (8 threads) | peak RSS | result |
|---|---|---|---|---|
| u16 `P=65521` | on / off | 4.71 s / 7.01 s | 419.9 / 426.6 MiB | OK / OK |
| u16 `P=65519` | on / off | 4.75 s / 6.57 s | 419.7 / 426.5 MiB | OK / OK |
| u32 `P=2097143` | on / off | 5.67 s / 7.70 s | 825.2 / 838.6 MiB | OK / OK |
| u32 `P=2097133` | on / off | 5.95 s / 8.05 s | 825.2 / 838.6 MiB | OK / OK |

The pruned and unpruned residue vectors are identical for all four primes (151 terms each).

**(b) Full `R`-table equality against `av12453_homog_split` built with the same
`-DMODP=65521`.** Both engines' `--dump-r` files are **byte-identical**:

| `N` | table entries `RSIZE` | non-zero entries in the dump | result |
|---|---|---|---|
| 40 | 224 680 | 224 676 | identical (`cmp`) |
| 60 | 1 117 520 | 1 117 509 | identical (`cmp`) |

Since both engines enumerate the identical index set `l = 1..N`, `a = 0..N-l`,
`q = 0..N-l-a`, `s < slen(a,q)` and emit every non-zero entry, byte equality of the two
dumps means **all 224 680 (resp. 1 117 520) table entries agree**.

The same dumps were also compared with the independent pure-Python reference in
`../pyref/` (`dump_N{40,60}_p{65521,2097143}.txt`) and are byte-identical there too:
224 676 / 224 680 entries at `N = 40` and 1 117 509 / 1 117 520 at `N = 60` for
`P = 65521` / `P = 2097143`.

In-binary `--engine both` (literal split, same storage) at `N = 40`:
`TABLE-MATCH: OK  all 224680 R entries agree`, for both u16 `P=65521` and
u32 `P=2097143`.

**(c) Cross-engine at scale.** `av12453_homog_split` at `N = 200`, `P = 65521`,
8 threads, `--prune` (154.04 s, 2 639.4 MiB) versus the new u16 engine (23.53 s,
1 303.6 MiB): **all 201 residues `n = 0..200` agree**.

**(d) Prefix consistency.** The residue vectors of the larger runs restrict exactly to
the smaller ones (0 mismatches): `N = 300` vs `N = 200` (201 terms) and `N = 200` vs
`N = 150` (151 terms), for both `P = 65521` (u16) and `P = 2097143` (u32).

**(e) Spill path.** `--spill` reproduces the non-spill residues exactly at `N = 60`
(both storage modes) and at `N = 200` (`P = 2097143`, 201 terms), and the spill file is
exactly `RSIZE * sizeof(ST)` bytes (`2 718 150 400` at `N = 300`, u32).

**(f) Kernel paths.** The NEON and portable (`-DNO_NEON`) builds agree and the
storage-width paths agree: `gemm_u32_65521` (u32 storage with a 16-bit prime) produces
byte-identical `--dump-r` output to `gemm_u16_65521`.

### Correction to the brief

The brief specifies the GEMM loop as `g2 = 1..W-3` (i.e. `tau1 = 2..W-2`). That drops
the `tau1 = 1` block, whose `A` is the `1 x 1` matrix `A[0][0] = C_1(y;0,0) = R[1][0](0,0) = 1`
contributing `C_{W-2}(y;0,s)` to `Phi_W(y;0,s)`. The implementation therefore uses
`g2 = 1..W-2` (`tau1 = 1..W-2`), matching the old engine. A build with the brief's range
fails immediately: `CERTIFY: FAIL at n=5  got 118 want 119`
(`tmp/variant_g2_upto_Wm3.cpp`).

Also, the brief describes the pruning as "`j <= W-q-2` (1-based points)" and says the
existing engine's `--prune` does the same; in fact `av12453_homog_split --prune` uses
`W-q` points per coordinate, two more than necessary. Both are exact; the sharper bound
used here is what the `degree-check` validates.
