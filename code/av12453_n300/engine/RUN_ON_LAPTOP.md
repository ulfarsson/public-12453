# Running the n = 300 CRT campaign on a laptop

Everything below is `engine_v2` (`av12453_gemm_split_v2.cpp`) plus the existing
harness in `../harness/`.  Nothing here needs the network.  Paths are written
relative to this directory (`.../n300_2026-09-02/engine_v2/`).

The whole pipeline is four steps: **primes -> build -> run -> reconstruct**.
Steps 3 and 4 are resumable; step 3 is the only long one.

---

## 0. What you need

* A C++17 compiler with OpenMP.
  * Linux: `g++` (>= 10) is enough — OpenMP is built in.
  * macOS: Apple `clang++` has **no** OpenMP. Either
    `brew install libomp` (then `build_primes.sh` finds it via
    `brew --prefix libomp` and adds `-Xpreprocessor -fopenmp … -lomp`), or
    `brew install gcc` and pass `--cxx g++-14`.
* `pypy3` (preferred) or `python3` for the harness scripts. No numpy needed.
* RAM: **6.9 GB** peak per prime for the u16 build at `N = 300`
  (10.5 GB for the u32 build with `--spill`). Only one job fits at a time on a
  16 GB machine; do not run two primes concurrently.
* Disk: the residue files are ~4 KB each. Negligible.

## 1. Primes

`../harness/primes_u16.txt` (77 primes below 2^16) and
`../harness/primes_u32.txt` (61 primes below 2^21) are already generated and
are what the current campaign uses. To regenerate them:

```bash
cd ../harness
pypy3 primes.py --n 300 --withheld 6 --outdir .
```

`B_300 = sum_m C(300,m)^2 |Av_m(1342)|` has 1136 bits, so 71 of the 77
16-bit primes carry the reconstruction and 6 are withheld as independent
checks. Use the u16 list unless you have a reason not to: u16 storage halves
the memory and needs no in-kernel reduction.

## 2. Build one binary per prime

The modulus is a compile-time constant, so each prime needs its own binary.

```bash
# Linux / g++  (the default)
./build_primes.sh --primes ../harness/primes_u16.txt \
                  --outdir bin_primes --jobs 8 --check-primality

# macOS, Apple clang + Homebrew libomp (auto-detected)
brew install libomp
./build_primes.sh --primes ../harness/primes_u16.txt --outdir bin_primes

# macOS, Homebrew gcc instead
./build_primes.sh --primes ../harness/primes_u16.txt --outdir bin_primes --cxx g++-14

# optional BLAS variants (see the warning below)
./build_primes.sh --primes ../harness/primes_u16.txt --outdir bin_primes_blas \
                  --cblas accelerate            # macOS / Accelerate
./build_primes.sh --primes ../harness/primes_u16.txt --outdir bin_primes_blas \
                  --cblas openblas              # Linux / OpenBLAS
```

`--dry-run` prints the compile commands without running them.
The binaries are named `bin_primes/av12453_gemm_<prime>`, which is exactly the
`--pattern` that `run_all.sh` expects. About 1-2 s per binary; with `--jobs 8`
the 77 binaries take under a minute.

**About `--cblas`.** The `-DUSE_CBLAS` path replaces the built-in 4x8 NEON
micro-kernel by one `cblas_dgemm` per `(j, g2)` and drops the staircase
blocking, so it *issues more multiply-adds*: 1.18x at N=100, 1.28x at N=200
and 1.35x at N=300 (exact enumeration, see README_v2.md section 4). It is a
win only if the BLAS is more than about 1.35x faster than the built-in kernel, which on this
aarch64 container it is not (the built-in kernel already runs at essentially
the full NEON FP issue width, 2.2e10 madd/s/thread). Benchmark
`--n 150 --threads <all>` both ways before committing a whole campaign to it,
and re-run the certification of step 5 for the BLAS binaries: a BLAS is exact
here only because every product and partial sum stays below 2^53, and a BLAS
that internally used FMA-with-different-rounding or extended precision would
still be exact, but one that used a fast-but-approximate path would not.
On this machine the CBLAS path has been correctness-tested only against the
naive reference in `cblas_stub/` (see README_v2.md §4).

## 3. Run the sweep

```bash
mkdir -p out300
bash ../harness/run_all.sh \
     --bindir  bin_primes \
     --primes  ../harness/primes_u16.txt \
     --n       300 \
     --threads 8 \
     --outdir  out300/residues \
     --extra-args "--prune"
```

* `--extra-args "--prune"` is required for the fast path (degree-aware point
  pruning; it is exact and is what every timing quoted here uses). Add
  `--spill` too if you use the u32 build and have less than 14 GB.
* `--threads` should be the number of physical performance cores. On an
  8-core VM one prime takes about 200 s at `N = 300` with engine v1; v2's
  parallel empty-stack phase removes most of the 63.5 s serial tail.
* Residues land in `out300/residues/<prime>.txt`, one file per prime, written
  atomically (`.tmp.<pid>` then `mv`), with a per-prime log in
  `out300/logs/<prime>.log` and a running summary in `out300/run_all.log`.
* Every binary self-checks on every run: binary64 reduction self-test,
  interpolation support check, and CERTIFY of `a_n mod p` against
  `repo/code/data/av12453_terms_0_150.txt` for `n <= 150`. A prime whose run
  fails any of these exits non-zero, its `.tmp` file is deleted, and
  `run_all.sh` records `FAIL` and moves on to the next prime.

### Resuming after an interruption

`run_all.sh` is resumable by design — just re-run the identical command.

* A prime with a complete `out300/residues/<prime>.txt` that passes the
  structural sanity check (`residue_io.py check FILE PRIME N`: right prime,
  right `N`, 301 consecutive `n residue` lines, every residue in `[0,p)`) is
  logged `SKIP` and not recomputed.
* A partial `.tmp.<pid>` file from a killed run is never promoted to
  `<prime>.txt`, so it is simply ignored; delete stray `*.tmp.*` files if you
  like. The interrupted prime is recomputed from scratch — there is no
  mid-prime checkpoint.
* A prime whose file exists but fails the sanity check is logged `WARN` and
  recomputed.
* If you suspect a *wrong but well-formed* residue file (e.g. bad RAM, a
  binary built with the wrong `-DMODP`), delete that file before resuming;
  the sanity check cannot see arithmetic errors. The withheld primes and the
  `n <= 150` CERTIFY in step 4 are the safety net that catches this.
* The exit status is 0 only if every prime ended `OK` or `SKIP`. Re-running
  after fixing whatever failed is safe and cheap.

To watch progress: `tail -f out300/run_all.log`.

## 4. Reconstruct

```bash
pypy3 ../harness/reconstruct.py \
      --residues-dir out300/residues \
      --n 300 \
      --output out300/terms_0_300.txt
```

This re-verifies every residue file against the certified `n <= 150` data,
computes the exact bound `B_300`, CRT-reconstructs from the smallest
sufficient prime set, checks `0 <= a_n <= B_n` for every `n`, checks that
every withheld prime agrees with the reconstruction, and checks that the
reconstructed prefix equals the data file exactly. It prints
`reconstructed=… primary=… withheld=… bound_bits=… product_bits=…` and writes
`n a_n` lines.

It is safe to run it on a partial residue directory: it will simply report
that the available product does not reach `B_300` yet, so you can use it as a
progress check.

## 5. Certification before you trust a new build

For a machine or compiler this engine has not run on before, do these three
(a few minutes total) before starting the 4-hour sweep:

```bash
./bin_primes/av12453_gemm_65521 --n 150 --threads 1 --prune   # CERTIFY: OK
./bin_primes/av12453_gemm_65521 --n 60  --threads 1           # unpruned: also
                                                              # degree-check +
                                                              # eval-check
# and compare a full R table against a second, differently-built binary:
./bin_primes/av12453_gemm_65521    --n 60 --threads 1 --dump-r a.txt
./bin/gemm_portable_65521          --n 60 --threads 1 --dump-r b.txt
cmp a.txt b.txt && echo "R tables byte-identical"
```

A `CERTIFY: OK … for 0 <= n <= 150` line plus `support-check: OK` on every run
is the contract `run_all.sh` relies on.
