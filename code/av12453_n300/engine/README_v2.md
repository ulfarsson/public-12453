# `av12453_gemm_split_v2` — changes with respect to the v1 engine

Directory: `code/av12453_n300/engine/` (developed in a scratch working directory; the files are kept here)

| file | what it is |
|---|---|
| `av12453_gemm_split_v2.cpp` | the v2 engine (1060 lines; v1 was 968) |
| `pristine/av12453_gemm_split.cpp` | byte-for-byte copy of the v1 source (sha256 `a617f2dc…`, identical to `engine/av12453_gemm_split.cpp` and to `campaign/av12453_gemm_split.cpp.used`) |
| `v1_to_v2.diff` | the complete v1 → v2 diff (193 lines, 9 hunks) |
| `build.sh` | as v1, plus `-Wall -Wextra` in `CXXFLAGS` and the stub-CBLAS builds |
| `build_primes.sh` | one binary per prime from a prime list, in parallel, Linux/macOS recipes |
| `RUN_ON_LAPTOP.md` | the four-step pipeline: primes → build → run → reconstruct, incl. resuming |
| `cblas_stub/` | `cblas.h` + `cblas_ref.c`: minimal header and a naive reference `cblas_dgemm`, used only to exercise the `-DUSE_CBLAS` code path |
| `bin/`, `logs/`, `tmp/` | binaries, raw run logs, scratch |

The v1 engine, its binaries and the running production campaign were not
touched: `engine/` and `campaign/` were only read from, and every binary run
from `engine/bin/` was executed with `--threads 1` or `--threads 2` at
`nice 19`.

**Nothing in the split kernel, the bands, the interpolation, the absorption or
the arithmetic changed.** v2 is v1 plus a parallel empty-stack phase, a
hardened `CERTIFY`, warning-clean flags, a tested `-DUSE_CBLAS` path and the
laptop packaging. Every residue file and every `--dump-r` file v2 produces is
byte-identical to v1's (verified below), so v2 is a drop-in replacement for
the campaign binaries.

---

## 1. Parallel empty-stack phase

### What was serial

`Engine::terms()` evaluates the empty-stack recursion of paper `eq:G`,

```
G[p][q] = sum_{h<p} G[h][mass-h-1]
        + sum_{h<q, delta=q-1-h}  ( delta == 0 ? G[p][h]
                                  : sum_{c<=p} sum_{s<slen(p-c,h)} R[delta][p-c][h][s] * G[c][s] )
```

over `mass = p+q = 1..N`. In v1 this was one serial triple loop. At `N = 300`
it is 40 502 249 970 modular multiply-adds and, per the v1 measurements,
**63.50 s of the 198.98 s eight-thread run — 32 %** — while seven of the eight
cores idled.

### What v2 does

The `mass+1` cells of one `mass` are **mutually independent**, so the loop over
`p` is parallelized with `#pragma omp parallel for schedule(dynamic,1)` and an
`reduction(+ : gm)` for the instrumented counter. The independence is exact,
not heuristic; the argument is written into the source above `terms()`:

* `G[h][mass-h-1]` and the `delta == 0` term `G[p][h]` (with `p+h = mass-1`)
  are cells of mass `mass-1`;
* in the main term `c <= p`, `s < slen(p-c, h)`, `h <= q-1`, so
  `c+s <= c + slen(p-c,h) - 1`, which is `p+h <= mass-1` when `c = p`
  (`slen(0,h) = h+1`) and `p+h-1 <= mass-2` when `c < p`
  (`slen(a,h) = a+h`, `a >= 1`).

So every read is of a cell of **strictly** smaller mass, and the implicit
barrier at the end of each `mass` iteration orders the generations. Each cell
keeps its own serial `u64` accumulation and `redP`/`partial` Barrett folds in
exactly the v1 order, so the arithmetic is untouched: **the result is
bit-identical for every thread count**, which is what the verification below
measures, not assumes.

`schedule(dynamic,1)` is needed because the cost of cell `(p,q)` is
`~ p*q*mass/2`, i.e. it varies by orders of magnitude across one `mass`. The
heaviest single cell is `~ mass^3/8` against a total of `~ mass^4/12`, a
fraction `1.5/mass`, so load imbalance stops mattering above `mass ~ 12` and
the phase is not limited by the granularity of the decomposition.

`-DNO_PARALLEL_EXTRACT` rebuilds the v1 serial loop with the v2
instrumentation; it exists only as the control for the timings below.

### New phase timers

v1 printed one `extract` number that also contained `finalize_tables()`. v2
adds, on stdout and in the `--sidecar` JSON:

```
# empty-stack phase: wall 0.792s  cpu 1.580s  (threads = 2, speed-up 2.00x)
# whole run: wall 11.241s  cpu 21.703s
```

with JSON keys `empty_stack_wall_s`, `empty_stack_cpu_s`, `total_cpu_s`
(`extract_s` keeps its v1 meaning). CPU time is `clock_gettime(CLOCK_PROCESS_CPUTIME_ID)`
summed over all threads, which is the number to compare on a machine that is
also running something else — as this one is.

### Measured: empty-stack phase, before and after

`N = 150`, `--prune`, `nice 19`, **while the 77-prime `N = 300` campaign was
using 8 of this box's 9 CPUs**. `SER` = `-DNO_PARALLEL_EXTRACT` (the v1 serial
loop with the v2 timers); `PAR` = the shipped v2. Two repetitions each; both
values are shown because the wall-clock spread is entirely contention.

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

Independently, in the byte-identity runs of §1 (which also print the timer):

| prime | v1 binary `extract` wall | v2 `empty-stack` wall | v2 `empty-stack` CPU |
|---|---|---|---|
| 65521, 1 thread | 1.668 s | 1.647 s | 1.440 s |
| 65521, 2 threads | 1.678 s | **0.792 s** | 1.580 s |
| 2097143, 1 thread | 2.430 s | 2.351 s | 2.105 s |
| 2097143, 2 threads | 2.409 s | **1.240 s** | 2.472 s |

Reading the numbers:

* **CPU time is essentially unchanged.** Serial 1.472-1.630 s vs parallel
  1.440-1.646 s (`u16`); 2.219-2.356 s vs 2.105-2.509 s (`u32`). The
  parallel-for construct costs at most a few per cent, which is inside the
  ±10 % run-to-run spread this loaded box produces. The work itself is
  identical — the `empty-stack madds` counter is `1 265 906 235` in every one
  of the 16 runs.
* **Wall time halves when two CPUs are actually free.** Best 2-thread wall:
  `0.822 s` vs the best serial `1.539 s` (`u16`) = **1.87x**;
  `1.261 s` vs `2.357 s` (`u32`) = **1.87x**. Against the v1 binary's own
  `extract` in the identity runs, `1.678 -> 0.792` = **2.12x** and
  `2.409 -> 1.240` = **1.94x**. The CPU/wall ratio in those runs is
  `1.580/0.792 = 2.00` and `2.472/1.240 = 1.99`, i.e. both threads really ran.
* **When the box is saturated there is no wall win**, and the table shows it
  honestly: the `PAR / 2 threads / rep 1` rows (`1.678 s`, `1.899 s`) were
  taken while the campaign held all 8 CPUs, and the CPU/wall ratio there is
  `0.94` and `1.27`.

### Projection to `N = 300` (not measured)

`engine/README.md` §8.1 gives the v1 `N = 300`, 8-thread, `u16` run as
`198.98 s` total with `63.50 s` of serial `extract`. At the ~2.0 CPU/wall ratio
measured on 2 threads, and with the heaviest-cell fraction `1.5/mass` making
imbalance negligible for `mass > 12`, an 8-thread empty-stack phase should land
near **9 s**, taking the `N = 300` run to roughly **145 s** (-27 %) and the
77-prime `u16` campaign from ~4.0 h to ~3.1 h. **This is an extrapolation, not
a measurement**: `N = 300` and thread counts above 2 were out of bounds for
this task, and 8-thread efficiency of this particular loop has not been
verified.

---

## 2. Hardened `CERTIFY`

### The hole

v1 loaded the truth file and then ran

```c
for (int n = 0; n <= N && n < (int)tr.size(); ++n) { ++nchecked; ... }
...
else printf("CERTIFY: OK  ... for 0 <= n <= %d\n", nchecked - 1);
```

so a truth file shorter than the run simply shrank the check, and an **empty**
truth file made it vacuous while still exiting 0. Reproduced against the
pristine v1 binary:

```
$ engine/bin/gemm_u16_65521 --n 10  --threads 1 --truth <empty file>
CERTIFY: OK  a_n mod P matches the data file for 0 <= n <= -1     rc=0
$ engine/bin/gemm_u16_65521 --n 150 --threads 1 --truth <first 100 lines>
CERTIFY: OK  a_n mod P matches the data file for 0 <= n <= 99     rc=0
```

The second line is the dangerous one for a campaign: a run that certifies only
`n <= 99` still reports `OK` and `run_all.sh` records it as a good prime.

### The fix

* `truth_required_entries(N) = min(N,150) + 1`. Fewer usable entries than that
  is a hard error with `exit(2)`, printing `CERTIFY: FAIL  truth file … supplies
  X entries, need Y (n = 0..Y-1)` on stdout and an explanation on stderr.
* The truth file is now loaded and length-checked **before the engine is
  constructed**, so a bad `--truth` fails in milliseconds instead of after the
  transfer. Every run prints what it is going to check:
  `# truth file …/av12453_terms_0_150.txt: 151 entries, CERTIFY will check n = 0..150`.
* The parser also rejects a line with no degree field, a line with no value
  field, and a degree out of order (v1 only caught the last), each with the
  file name and line number.
* The default truth path is unchanged:
  `code/data/av12453_terms_0_150.txt`.

Note `exit(2)` — distinct from the `1` used for a failed check — so
`run_all.sh` still records `FAIL … rc=2` and deletes the `.tmp` file.

### Measured

| binary | `--n` | `--truth` | rc | stdout |
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

Command: `bash tmp/truthtest.sh` — reproduced in `logs/` and in §7 below.

---

## 3. `-Wall -Wextra`, and the README counter correction

`build.sh` now carries

```
CXXFLAGS=${CXXFLAGS:--O3 -march=native -std=c++17 -fopenmp -funroll-loops -Wall -Wextra}
CFLAGS=${CFLAGS:--O3 -march=native -std=c11 -Wall -Wextra}      # cblas_stub/cblas_ref.c
```

and the whole build is warning-free — every flavour, `gemm_u16_65521`,
`gemm_u16_65519`, `gemm_u32_2097143`, `gemm_u32_2097133`, `gemm_u32_65521`
(`-DSTORE_BITS=32`), `gemm_portable_65521` (`-DNO_NEON`), `gemm_modp`,
`gemm_cblas_65521` and `gemm_cblas_2097143` (`-DUSE_CBLAS`), plus the
`-DNO_PARALLEL_EXTRACT` control builds. g++ (Debian 14.2.0-19) 14.2.0 emitted
**zero** diagnostics: v1's source was already clean under `-Wall -Wextra`, and
the v2 additions kept it that way. (Nothing had to be "fixed"; the flags were
simply never enabled, so this was previously unverified.)

### Corrected counters

`engine/README.md` §8.2 says, of the unpruned `N = 150` run:

> Unpruned (`N = 150`): structural `446 984 070 878`, issued `623 043 782 656`.

Both numbers are wrong. Re-measured here on the **pristine v1 binary** and on
v2 (`--n 150 --threads 2`, no `--prune`), which agree exactly:

| quantity | `engine/README.md` | measured (v1 **and** v2) |
|---|---|---|
| `split madds structural`, unpruned `N = 150` | 446 984 070 878 | **446 984 370 494** |
| `split madds issued`, unpruned `N = 150` | 623 043 782 656 | **623 043 607 808** |

The derived statement in the same paragraph survives: with the pruned figures
(structural 235 381 173 728, issued 325 738 808 704) the degree pruning removes
`1 - 235 381 173 728/446 984 370 494 = 47.3 %` of the structural work, and the
padding overhead is `325 738 808 704/235 381 173 728 = 1.384`.

`engine/README.md` is read-only for this task, so the correction is recorded
here rather than edited into that file. The two unpruned runs also produced
byte-identical residue files and `CERTIFY: OK … 0 <= n <= 150`,
`degree-check: OK`, `eval-check: OK`.

---

## 4. The `-DUSE_CBLAS` path, tested

v1 shipped a `-DUSE_CBLAS` variant that had **never been compiled**: this
container has no `cblas.h`, so `build.sh` printed the "no cblas.h on this
machine, skipped" branch every time. It is the path the RUN_PLAN proposes for a
native Mac build against Accelerate, so it needed at least a correctness test.

### The stub

`cblas_stub/cblas.h` declares the two CBLAS enums and `cblas_dgemm` with the
reference (Netlib / OpenBLAS / Accelerate) signature — nothing else, so a
source that compiles against it also compiles against a real CBLAS.
`cblas_stub/cblas_ref.c` implements it as a naive `i-k-j` triple loop in C11.
It supports exactly the one call the engine makes,

```c
cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans,
            MPb, nsPad, K, 1.0, Ap, K, Bp, nsPad, 1.0, C, nsPad);
```

and `abort()`s with a diagnostic on any other order, transpose, `alpha`,
`beta` or inconsistent leading dimension, so it cannot silently paper over a
mis-issued call. It is a **correctness reference only** — it is a naive loop
and says nothing about the speed of a real BLAS.

Why a different summation order still gives the same bits: every `A` and `B`
entry is an integer in `[0,P)` and, by the engine's `PRODLIMIT` accounting,
every `C` entry stays a non-negative integer below `2^53` at all times. Below
`2^53` binary64 represents every integer exactly and integer `+` and `*` are
exact, so every partial sum is exact and the result is independent of the
order of accumulation. That is the same argument that makes the blocked NEON
kernel exact, and it is why a real BLAS is admissible here too.

### Result

`g++ -O3 -march=native -std=c++17 -fopenmp -funroll-loops -Wall -Wextra
-DMODP=<p>ull -DUSE_CBLAS -Icblas_stub av12453_gemm_split_v2.cpp tmp/cblas_ref.o
-o bin/gemm_cblas_<p>`, run with `--threads 1 --prune`:

| prime | `N` | residues | `--dump-r` | `reduce_ops` micro-kernel / CBLAS | `split_madds_issued` micro-kernel / CBLAS | split time |
|---|---|---|---|---|---|---|
| 65521 | 60 | **byte-identical** | **byte-identical** | 1 618 432 / 1 618 432 | 1 670 940 544 / 1 670 940 544 | 0.111 s / 0.333 s |
| 65521 | 100 | **byte-identical** | **byte-identical** | 12 495 392 / 12 495 392 | 29 902 907 808 / 35 379 881 888 | 1.695 s / 6.626 s |
| 2097143 | 60 | **byte-identical** | **byte-identical** | 1 618 432 / 1 618 432 | 1 670 940 544 / 1 670 940 544 | 0.101 s / 0.354 s |
| 2097143 | 100 | **byte-identical** | **byte-identical** | 27 198 432 / 27 198 432 | 29 902 907 808 / 35 379 881 888 | 1.775 s / 7.555 s |

Both builds also pass `selftest`, `support-check` and `CERTIFY` on every run,
and the CBLAS build additionally passes the in-binary literal-split comparison
(`--engine both`, `N = 40`).

### Does the CBLAS path use the same `PRODLIMIT` reduction schedule?

**Yes, exactly the same one.** The schedule lives in the `(w, j, tau1)` driver
loop, outside the `#ifdef USE_CBLAS`:

```c
if (pc + (u64)K > PRODLIMIT) { reduce_block(C, MP*nsPad); rd += MP*nsPad; pc = 1; }
pc += (u64)K;
```

`K = tau1`, `MP` and `nsPad` do not depend on the kernel, so the reductions
happen at identical `(w, j, tau1)` and cover identical buffers. The
`reduce_ops` counter is the numerical confirmation: it is equal for the two
builds at every `(prime, N)` tested — including `27 198 432` for `P = 2097143`
at `N = 100`, where the `PRODLIMIT = 2048` schedule fires many intermediate
reductions, versus `12 495 392` for `P = 65521` where only the per-`(W,j)`
final reduction runs. The bound also stays *valid* for CBLAS: the accounting
charges `K` products per block per `C` entry, which is the maximum, whereas
the blocked kernel actually issues only `K - mstart` for entries in a
staircase-skipped block. CBLAS issues the full `K` — inside the same budget.

`split_madds_issued` is the one counter that legitimately differs, and only
where the staircase matters: at `N = 60` every `ns = w-2 <= 58` fits in one
`NCB = 64` column block with `mstart = 0`, so the two kernels issue exactly the
same FMAs; at `N = 100` the second column block has `mstart > 0` and the CBLAS
path, which drops the staircase blocking, issues `35 379 881 888 /
29 902 907 808 = 1.183x` as many.

The naive reference is 3.9x - 4.3x slower than the built-in NEON micro-kernel
here, as expected of a triple loop. **This is a correctness test only.**

Whether Accelerate or OpenBLAS beats the built-in kernel on a real Mac has to
be benchmarked there, and the handicap grows with `N`. A short enumeration of
the two counters (`tmp/count_issued.py`, which reproduces the measured
`split_madds_issued` at `N = 60` and `N = 100` and the v1 README's blocked
figures at `N = 150, 200, 300` exactly) gives:

| `N` | blocked issued | CBLAS issued | CBLAS / blocked |
|---|---|---|---|
| 60 | 1 670 940 544 | 1 670 940 544 | 1.000 |
| 100 | 29 902 907 808 | 35 379 881 888 | 1.183 |
| 150 | 325 738 808 704 | 400 718 307 712 | 1.230 |
| 200 | 1 752 053 397 536 | 2 243 333 132 320 | 1.280 |
| 300 | 18 819 551 098 976 | 25 473 600 960 608 | **1.354** |

So at `N = 300` a BLAS must be more than **1.354x** faster than the built-in
kernel just to break even, and the built-in kernel already sustains
~2.2e10 madd/s/thread, essentially the full NEON FP issue width.

---

## 5. Laptop packaging

### `build_primes.sh`

The modulus is a compile-time constant, so a CRT sweep needs one binary per
prime. `build_primes.sh` builds them all in parallel and names them exactly as
`harness/run_all.sh`'s default `--pattern` expects
(`<outdir>/av12453_gemm_<prime>`).

```
./build_primes.sh --primes FILE [--outdir DIR] [--jobs K] [--store 16|32]
                  [--cblas none|accelerate|openblas|stub] [--src FILE]
                  [--cxx CXX] [--extra "flags"] [--dry-run] [--check-primality]
```

* **Linux / g++** (auto-detected): `-O3 -march=native -std=c++17 -funroll-loops
  -Wall -Wextra -fopenmp`.
* **macOS / Apple clang**: `-march=native` is probed first, then `-mcpu=native`,
  then `-mcpu=apple-m1`; Apple clang has no OpenMP, so the script looks for
  Homebrew `libomp` via `brew --prefix libomp` and, if found, switches to
  `-Xpreprocessor -fopenmp -I<prefix>/include` + `-L<prefix>/lib -lomp`. If
  `libomp` is missing it warns loudly and builds single-threaded rather than
  failing silently.
* **macOS / Homebrew g++**: `--cxx g++-14` and it behaves like the Linux case.
* `--cblas accelerate` adds `-DUSE_CBLAS -DACCELERATE_NEW_LAPACK` with the
  vecLib headers from `xcrun --show-sdk-path` and `-framework Accelerate`;
  `--cblas openblas` finds `cblas.h` in the usual places and links
  `-lopenblas`; `--cblas stub` builds against `cblas_stub/` (correctness only).
* `--check-primality` trial-divides every modulus and refuses any `p >= 2^21`
  (outside the exactness proof).
* `--dry-run` prints the compile commands and stops.
* After building it runs one smoke test (`--n 30 --threads 1`) and exits
  non-zero if any binary failed to build or the smoke test failed.

Verified here on a 3-prime list (65521, 65519, 2097143) with `--jobs 2`:
`# built 3 / 3 binaries`, smoke test `CERTIFY: OK … 0 <= n <= 30`; and the
resulting directory drives `harness/run_all.sh` unchanged —
`--dry-run` resolves `tmp/bin_test/av12453_gemm_<prime>` for all three, and a
real `N = 60` sweep gave `SUMMARY ok=3 skip=0 fail=0`, with an immediate re-run
giving `SUMMARY ok=0 skip=3 fail=0` (the resume path).

### `RUN_ON_LAPTOP.md`

The four-step pipeline end to end: **primes** (`harness/primes.py`, and why the
u16 list of 77 is the default: 71 primary + 6 withheld against the 1136-bit
`B_300`), **build** (`build_primes.sh`, per-platform), **run**
(`harness/run_all.sh … --extra-args "--prune"`, thread and RAM guidance, the
per-run self-checks), **reconstruct** (`harness/reconstruct.py`), plus a
"Resuming after an interruption" section (what `SKIP` means, why a stray
`.tmp.<pid>` is harmless, that there is no mid-prime checkpoint, and the one
case — a well-formed but arithmetically wrong file — that the sanity check
cannot see and the withheld primes must catch) and a five-minute certification
checklist for a machine this engine has not run on before.

Nothing in it was executed at `N = 300`; the only pipeline runs made here were
the `N = 60` sweep above.

---

## 6. What v2 does **not** change

* The split kernel, the micro-kernel, the packing, the pruning, the
  interpolation, the bands/D term, the absorption, the spill path and all
  arithmetic are byte-for-byte the v1 code. The `v1_to_v2.diff` is 193 lines
  in 9 hunks, all of them in `terms()`, `load_truth_mod()`, `main()`'s
  reporting, and comments.
* The residue-file header still reads
  `# engine av12453_gemm_split storage <s> threads <k> prune <0|1>`
  (**not** `_v2`) — deliberately, so that v2's output files are byte-identical
  to v1's and a campaign can be finished with a mixture of both. The engine
  name in the *stdout* banner is likewise unchanged; the v2 build is
  identified by the extra `# truth file …` and `# empty-stack phase: …` lines.
* `--dump-r`, `--sidecar` (which gains three keys and loses none), `--spill`,
  `--engine naive|both`, `--prune`, the CLI and the exit-status contract are
  unchanged. `run_all.sh` and `reconstruct.py` need no modification.
* The exactness argument, `PRODLIMIT`, the `selftest`, `support-check`,
  `degree-check`, `eval-check` and `TABLE-MATCH` are untouched and all still
  pass.

Retained v1 cross-checks, re-run on the v2 binaries (`tmp/phase3.sh`):

| check | result |
|---|---|
| `--engine both` (literal split), `N = 40`, CBLAS build | `TABLE-MATCH: OK  all 224680 R entries agree`, `CERTIFY: OK` |
| `R` table `N = 60`: `gemm_u16_65521` vs `gemm_portable_65521` (`-DNO_NEON`) | byte-identical |
| `R` table `N = 60`: `gemm_u16_65521` vs `gemm_u32_65521` (`-DSTORE_BITS=32`) | byte-identical |
| `R` table `N = 60`: `gemm_u16_65521` vs `gemm_cblas_65521` (`-DUSE_CBLAS`) | byte-identical |
| `--spill` vs in-RAM residues, `N = 60`, `P = 2097143` | identical; spill file 4 470 080 B = `RSIZE * 4` |
| `selftest`, `support-check`, `CERTIFY` | OK on all 53 logged runs (0 FAIL, 0 VIOLATION) |
| `degree-check`, `eval-check` (unpruned runs) | OK |

---

## 7. Exact commands

Everything below was run at `nice 19` while the 77-prime `N = 300` production
campaign was using 8 threads on the same 9-CPU box. No run used more than
2 threads, `N > 150` or ~1 GB of RSS, and `engine/` and `campaign/` were only
read from.

```bash
cd code/av12453_n300/engine

# ---- build (warning-free; see §3)
./build.sh
g++ -O3 -march=native -std=c++17 -fopenmp -funroll-loops -Wall -Wextra \
    -DMODP=65521ull -DNO_PARALLEL_EXTRACT av12453_gemm_split_v2.cpp \
    -o bin/gemm_u16_65521_serialextract          # serial-extract control
g++ ... -DMODP=2097143ull -DNO_PARALLEL_EXTRACT ... -o bin/gemm_u32_2097143_serialextract

# ---- (1) byte-identity of residues and --dump-r, v1 vs v2  (8 pairs)
for B in gemm_u16_65521 gemm_u32_2097143; do for N in 100 150; do for T in 1 2; do
  nice -n 19 ../engine/bin/$B --n $N --threads $T --prune \
       --out v1.res --dump-r v1.dump
  nice -n 19 ./bin/$B        --n $N --threads $T --prune \
       --out v2.res --dump-r v2.dump
  cmp v1.res v2.res && cmp v1.dump v2.dump
done; done; done                                  # scripted as tmp/ident.sh

# ---- (2) CERTIFY hardening
bash tmp/truthtest.sh          # 13 cases, v1 and v2, tabulated in §2

# ---- (3) unpruned N=150 counters, v1 and v2
nice -n 19 ../engine/bin/gemm_u16_65521 --n 150 --threads 2 --out unpruned_v1.res
nice -n 19 ./bin/gemm_u16_65521         --n 150 --threads 2 --out unpruned_v2.res

# ---- (4) CBLAS path
gcc -O3 -march=native -std=c11 -Wall -Wextra -c cblas_stub/cblas_ref.c -o tmp/cblas_ref.o
g++ ... -DMODP=65521ull -DUSE_CBLAS -Icblas_stub av12453_gemm_split_v2.cpp \
    tmp/cblas_ref.o -o bin/gemm_cblas_65521
for N in 60 100; do
  nice -n 19 ./bin/gemm_u16_65521   --n $N --threads 1 --prune --out r.res --dump-r r.dump --sidecar r.json
  nice -n 19 ./bin/gemm_cblas_65521 --n $N --threads 1 --prune --out c.res --dump-r c.dump --sidecar c.json
  cmp r.res c.res && cmp r.dump c.dump
done                                              # and the same for P = 2097143

# ---- (5) packaging
./build_primes.sh --primes tmp/primes_test.txt --outdir tmp/bin_test --jobs 2 --check-primality
bash ../harness/run_all.sh --bindir tmp/bin_test --primes tmp/primes_test.txt \
     --n 60 --threads 1 --outdir tmp/rundry/residues --extra-args "--prune"

# ---- (6) certification of v2 at N=150, 1 thread
for P in 65521:gemm_u16_65521 2097143:gemm_u32_2097143; do
  p=${P%%:*}; b=${P##*:}
  nice -n 19 ../engine/bin/$b --n 150 --threads 1 --prune --out t6/v1_$p.res
  nice -n 19 ./bin/$b         --n 150 --threads 1 --prune --out t6/v2_$p.res --sidecar t6/v2_$p.json
  cmp t6/v1_$p.res t6/v2_$p.res
done
```

Raw logs of every run are in `logs/`; the driver scripts are `tmp/phase2.sh`,
`tmp/phase3.sh`, `tmp/ident.sh`, `tmp/cblas.sh`, `tmp/truthtest.sh`.

---

## 8. Notes and limitations

* **8-thread scaling of the empty-stack phase was not measured.** The
  production campaign owns 8 of this box's 9 CPUs, so every measurement here
  is at 1 or 2 threads. The 2-thread wall speed-ups above are the direct
  evidence; the projection to 8 threads rests on the work-distribution
  argument (heaviest cell / total = `1.5/mass`, so imbalance is negligible for
  `mass > 12`) and has not been confirmed.
* **`N = 300` was not run**, in either version, per the task constraints. The
  `N = 300` figures quoted for v1 are `engine/README.md`'s.
* **Wall-clock timings on this box are contaminated** by the campaign. The same
  binary and phase measured `0.822 s` and `1.678 s` of wall time in two runs
  minutes apart. CPU time is the number to compare, and even that carries a
  ±10 % run-to-run spread here.
* The two `-DNO_PARALLEL_EXTRACT` control binaries and the two `_serialextract`
  builds exist only for the before/after timing; they are not part of the
  campaign build set.
* `engine/README.md` cannot be edited from this task, so its two wrong
  unpruned `N = 150` counters are corrected in §3 here instead.
* The `--cblas accelerate` and `--cblas openblas` recipes in `build_primes.sh`
  are **untested** — there is no BLAS and no macOS on this container. Only the
  `--cblas stub` path was compiled and run.
