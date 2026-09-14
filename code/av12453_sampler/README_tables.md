# `tables/` — double-precision R and G tables for the Av(12453) sampler

Produced for `SAMPLER_BRIEF.md` (2026-09-03).  Nothing here enters the paper.
The repository is read-only; the mathematics is the proved reduced `d = 2`
recurrence of `paper/av12453_polytime.tex` Sections 5 and 7.

## Files

| file | what |
|---|---|
| `tables.cpp` | builder: direct reduced recurrence in increasing grade, OpenMP over rows, writes AVR1 |
| `avr_table.hpp` | AVR1 layout + reader for C++ consumers (`sampler.cpp`); included by `tables.cpp` |
| `avr_table.py` | AVR1 reader for Python/pypy3: `G(p,q)`, `R(l,a,q,s)`, `K(l,p,q,c,t)`, index functions, CLI |
| `avr_check.cpp` | tiny C++ reader/printer, used to cross-check C++ vs Python indexing |
| `build.sh` | builds `tables` and `avr_check` |
| `check_terms.py` | `G(n,0)` vs `repo/code/data/av12453_terms_0_300.txt` |
| `check_r.py` | every `R` entry vs an exact dump of `repo/code/av12453_n300/pyref/ref.py` |
| `check_prefix.py` | bit-identity of two tables of different `N` on their shared entries |
| `validate.sh` | runs the whole check list |
| `N60.avr`, `N100.avr`, `N150.avr` | the tables used during development (`N40.avr` is the validation table) |

## Usage

```sh
sh build.sh
./tables --N 150 --threads 4 --out N150.avr        # add -v for per-grade progress
python3 avr_table.py N150.avr --info
python3 avr_table.py N150.avr --G 150,0 --R 5,2,3,1 --row 5,2,3 --terms 0:10
pypy3   avr_table.py N150.avr --mmap --G 150,0     # shared mapping, no 342 MB copy
./avr_check N150.avr --info --R 5,2,3,1
```

C++ consumers:

```cpp
#include "avr_table.hpp"
avr::Table T;  std::string err = T.load("N150.avr");   // "" on success
double g = T.G(p, q);
double r = T.R(l, a, q, s);          // zero-extended outside the support
double k = T.K(l, p, q, c, t);       // = R(l, p-c, q, t) for c <= p, else 0
const double *row = T.row(l, a, q);  // contiguous, length avr::Layout::slen(a,q)
```

## What is computed

`slen(a,q) = q+1` if `a = 0`, else `a+q` (the support of `R_{l,a}(q,.)` is
`{0..q}` resp. `{0..a+q-1}`).

```
R_{l,a}(q,s) = sum_{h=0}^{a-1} R_{l,h}(a+q-h-1,s)                   [early band]
             + sum_{r=0}^{q-1} R_{l+q-r-1,a}(r,s)                   [last band]
             + D_{l,a}(q,s)                                         [endpoints]
             + sum_{l1=1}^{l-2} sum_{a1=0}^{a} sum_m
                  R_{l1,a1}(q,m) R_{l-1-l1,a-a1}(m,s)               [interior]
D_{1,a}(q,s) = [a=0][q=s],   D_{l,a}(q,s) = 2 R_{l-1,a}(q,s)  (l >= 2)

G_{(0,0)} = 1;  for (p,q) != (0,0)
G_{(p,q)} = sum_{h=0}^{p-1} G_{(h,p+q-1-h)}
          + sum_{h=0}^{q-1} ( delta = q-1-h == 0 ? G_{(p,h)}
                            : sum_{a=0}^{p} sum_v R_{delta,a}(h,v) G_{(p-a,v)} )
a_n = G_{(n,0)}.
```

Both readers extend `R` by `R_{0,a}(q,s) = [a=0][q=s]` (the identity kernel
`K_0`), which the sampler needs for a block of size 0.

The reduced grade `w = l+a+q` is a topological order: every input of a row of
grade `w` has grade `< w`, so all rows of one grade are computed in parallel
(`#pragma omp parallel for schedule(dynamic,1)` over the `(l,a)` pairs, `q`
determined by `w`).  The empty-stack phase is likewise parallel over `p` at
fixed `p+q`.  No evaluation/interpolation scheme is used anywhere — that is
what would be unstable in floating point; here every summand is nonnegative,
so nothing cancels.

## File format `AVR1`

Native little-endian:

```
int32  magic = 0x41565231
int32  N
G      doubles, p = 0..N, q = 0..N-p                              nested in that order
R      doubles, l = 1..N, a = 0..N-l, q = 0..N-l-a, s = 0..slen(a,q)-1
```

Indexing (identical in `avr_table.hpp` and `avr_table.py`): rows of a fixed
`(l,a)` are contiguous in `q`, with `pref(a,q) = sum_{q'<q} slen(a,q')`
(`= q(q+1)/2` for `a = 0`, `= a q + q(q-1)/2` for `a >= 1`), so the offset of
`R_{l,a}(q,s)` inside the R block is `qbase[l,a] + pref(a,q) + s`.  The
contiguity in `q` is also what the builder's inner loop exploits.

## Precision

Binary64 throughout.  All terms of both recurrences are nonnegative, so the
only error is rounding; the measured relative error of `G(n,0)` against the
exact terms is `7.0e-16` at `N = 60`, `1.3e-14` at `N = 100` and `3.1e-13` at
`N = 150` — three orders of magnitude inside the `1e-11` requirement, and far
below the `1e-13`-per-decision level at which the sampler's uniformity is
stated in the brief.  `a_200` has about 760 bits, well inside the binary64
exponent range, but **do not build beyond `N = 200`** without scaled
arithmetic.  `tables` prints a warning above `N = 200`.

The build is deterministic: the 1-thread and 4-thread outputs are
byte-identical, and a table built at `N1` is byte-identical to a table built
at `N2 > N1` on every entry both store (`check_prefix.py`).

## Measurements (this machine: aarch64, 9 cores, g++ 14.2, `-O3 -march=native`)

| N | R rows | R doubles | file | build, 4 threads | peak RSS | sha256 (first 16) |
|---|---|---|---|---|---|---|
| 40 | 11 480 | 224 680 | 1 804 336 B (1.7 MiB) | 0.017 s | 3 MiB | `4fe79faea2950a5c` |
| 60 | 37 820 | 1 117 520 | 8 955 296 B (8.5 MiB) | 0.202 s | 11.5 MiB | `deb3c31b44f91ec9` |
| 100 | 171 700 | 8 504 200 | 68 074 816 B (64.9 MiB) | 8.00 s | 68.1 MiB | `e5dd0e69fed1d2ae` |
| 150 | 573 800 | 42 759 425 | 342 167 216 B (326.3 MiB) | 168.3 s | 329.8 MiB | `06e674fd7d245168` |

Interior-split multiply-adds: `1.379e8` (N=40), `2.483e9` (N=60), `9.265e10`
(N=100), `1.619e12` (N=150) — the brief's `N^7/1008` estimate is accurate to
5%.  Rate at N=150: `9.7e9` madd/s on 4 threads.  Single-thread N=100 takes
30.96 s against 7.92 s on 4 threads (3.91x).

Both phases are cheap in memory: the tables themselves dominate, so `N = 150`
fits comfortably in the 4 GB budget.
