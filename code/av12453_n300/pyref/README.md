# `pyref/`: independent reference for the reduced d = 2 recurrence

`ref.py` is a pure-Python implementation (run it with PyPy) of the reduced
`d = 2` recurrence for `|Av_n(12453)|`.  It was written from the printed
equations of the paper `../../../paper/av12453_polytime.tex` alone, without
reading or reusing any other code of the repository or the notes on the
homogeneous split; besides the manuscript it consults only the certified
data file `../../data/av12453_terms_0_150.txt` (SHA-256
`f5ab4017ec65a661d8fbcd84d2f7893afe5e2c695dd082ace58399f7960340fc`).  It is
the independent implementation against which the GEMM engine of
`../engine/` is checked.

## What it implements

* the exact support `eq:support-d2` (Lemma "Exact two-threshold support"),
  transported through the first-coordinate translation `eq:d2-translation`,
  and the reduced entries `eq:R-definition`,
  `R_{l,a}(q,s) = K_l((a,q),(0,s))`; the stored row length is
  `scount(a,q) = q+1` for `a = 0` and `a+q` for `a >= 1`;
* the reduced recurrence `eq:R-recurrence` with its `D` term, memoized in
  increasing reduced grade `w = l+a+q` (`w = 1..N` by default).  The split is
  the literal triple sum over `(l1, a1, m)`: no homogeneity slices, no
  evaluation points, no interpolation;
* the empty-stack recurrence `eq:G` (Corollary "Empty-stack recurrence"),
  with `eq:T`, `eq:U` and `eq:answer-G`, in the reduced variables:
  `a_n = G_(n,0)`;
* the second-coordinate translation `eq:d2-second-translation`, only as an
  extra check (`--trans-check`), not in the recurrence.

The equations as implemented are written out in the docstring of `ref.py`.
Arithmetic is exact Python integers by default.  With `--mod P` every stored
row is reduced to `[0,P)`; inside the split, products are accumulated without
reduction while the running total is provably below `2^62` (the row is
reduced whenever the number of accumulated products would exceed
`2^62/(P-1)^2`), which keeps PyPy on its machine-word integer path.

## Command line

```
pypy3 ref.py N [--mod P] [--dump-r FILE] [--dump-all] [--terms FILE]
               [--max-grade G] [--support-check M] [--support-pad K]
               [--brute B] [--trans-check] [--check-data [FILE]]
               [--progress] [--stats FILE]
```

* `--dump-r FILE`: one line `l a q s value` per entry inside the support of
  every row with `l+a+q <= G` (`G = --max-grade`, default `N`), sorted by
  `(l, a, q, s)`, single spaces, LF line ends, no header.  The value is the
  residue in `[0,P)` with `--mod P` and the exact integer otherwise.  Entries
  whose value is 0 are omitted unless `--dump-all` is given.  Over the
  integers no entry inside the support vanishes (the support lemma is an
  equality of sets, checked for every row of grade `<= 60`), but modulo `P`
  some do: 4 of the 224 680 entries at `N = 40` and 11 of the 1 117 520 at
  `N = 60` vanish modulo 65521, none modulo 2097143.  After its header line
  `# P <prime> N <N>`, the engine's `--dump-r` file has the same format.
* `--terms FILE`: one line `n a_n` for `n = 0..N` (the residue under
  `--mod P`).
* `--check-data [FILE]`: compare the terms with the data file (default
  `../../data/av12453_terms_0_150.txt`, located relative to `ref.py`),
  reduced modulo `P` under `--mod`.
* `--support-check M [--support-pad K]`: recompute every row of grade `<= M`
  with `K` extra terminal coordinates (default 3) and check that they vanish,
  and in exact arithmetic also that no entry inside the support vanishes.
* `--brute B`: brute-force `|Av_n(12453)|` for `n <= B` and compare.
* `--trans-check`: check `R_{l,a}(q+1,s+1) = R_{l,a}(q,s)` for `s >= a-1`.
* `--max-grade G`: largest reduced grade computed; it must be at least
  `N-1`, which is all the terms need.
* `--stats FILE`: a JSON-style sidecar with timings, counts and the SHA-256
  of the dump.

The exit status is non-zero if any requested check fails.

Index convention of the dump: `l >= 1` is the block size, `a >= 0` the
reduced first control coordinate (`a = p - c` in `eq:d2-translation`),
`q >= 0` the second source coordinate and `s` the second terminal
coordinate; the value is `R_{l,a}(q,s) = K_l((a,q),(0,s))`.  Rows are not
compressed by the second-coordinate translation: every `s` of the support is
present.  Values that do not depend on any implementation:
`R_{1,0}(0,0) = 1`, `R_{1,0}(2,0) = 3`, `R_{1,1}(1,0) = 2`, `R_{1,2}(0,0) = 2`,
`R_{1,2}(1,1) = 3` (the last two are printed in the paper) and
`R_{2,0}(0,0) = 2`.

Helpers:

* `compare_dump.py A B [--mod P] [--max-grade G]` compares two dumps by key
  `(l,a,q,s)`.  It skips `#` lines and treats a missing key as the value 0,
  so dumps with and without zero lines compare equal; `--mod P` reduces both
  sides first, and `--max-grade G` restricts the comparison to `l+a+q <= G`.
  Exit status 0 iff the dumps agree.
* `madd_count.py [N ...]` evaluates the closed form of the number of split
  multiply-adds of `ref.py`,
  `count(N) = sum_{l+a+q<=N, l>=3} (l-2) * sum_{a1+a2=a} sum_{m<scount(a1,q)} scount(a2,m)`.
* `test_brute.py` validates the brute-force containment test of `--brute`
  on other patterns.

## Verification results

All checks pass.

| check | command | result |
|---|---|---|
| exact `a_n`, `n <= 60` | `ref.py 60 --check-data` | 61/61 terms equal `av12453_terms_0_150.txt` |
| exact `a_n`, `n <= 40` | `ref.py 40 --check-data` | 41/41 |
| residues `n <= 100` modulo 2097143 | `ref.py 100 --mod 2097143 --check-data` | 101/101 terms equal the data file modulo `P` |
| residues `n <= 60` modulo 65521 and 2097143 | `--check-data` in every dump run | 61/61 each |
| support statement, exact, all rows of grade `<= 60` | `ref.py 60 --support-check 60 --support-pad 3` | 37 820 rows with 3 extra terminal coordinates each: no non-zero entry outside the support and no zero entry inside it (the lemma is an equality, so both halves hold over the integers) |
| support statement modulo 65521 / 2097143, grade `<= 60` | `--support-check 60` | no non-zero entry outside the support; 11 (resp. 0) entries inside it vanish modulo `P`, which is allowed |
| support statement, exact, grade `<= 40` | `ref.py 40 --support-check 40` | 11 480 rows, no violation |
| brute force `n <= 8` | `ref.py 8 --brute 8` (all `C(n,5)` position subsets, standardization, comparison with `12453`) | `1, 1, 2, 6, 24, 119, 694, 4581, 33286`, equal to the recurrence and the data file |
| the containment test itself | `test_brute.py` | `Av(231)` gives the Catalan numbers `1,1,2,5,14,42,132`; `Av(1342)` gives `1,1,2,6,23,103,512,2740` (Bona, A022558); `Av(12345)` gives `1,1,2,6,24,119,694,4582`, equal to an independent RSK/hook-length computation and different from `Av(12453)` at `n = 7` (4582 against 4581) |
| second-coordinate translation `eq:d2-second-translation` | `ref.py 60 --trans-check` (exact) | 557 845 instances of `R_{l,a}(q+1,s+1) = R_{l,a}(q,s)` for `s >= a-1` |
| values printed in the paper | exact dump at `N = 40` | `R_{1,2}(1,1) = 3`, `R_{1,2}(0,0) = 2` |
| modular against exact tables | `compare_dump.py EXACT MOD --mod P` | all entries agree after reduction at `N = 40` (224 680) and `N = 60` (1 117 520), for both primes |
| truncation independence | `compare_dump.py N40_p65521 N60_p65521 --max-grade 40` | the `N = 40` dump is exactly the grade `<= 40` part of the `N = 60` dump |
| stored-entry count | counted at run time | `N(N+1)(N^2+N+4)/12` of `eq:d2-first-reduced-counts`: 224 680 (`N = 40`), 1 117 520 (`N = 60`), 8 504 200 (`N = 100`) |

The dumps used for the comparison with the engine are reproduced by these
commands, with the following line counts and SHA-256 values:

| command | lines | SHA-256 |
|---|---|---|
| `ref.py 40 --mod 65521 --dump-r F` | 224 676 | `a2622a062ed7468dd21ea5932b41fcb8543e93b09891cc651327ac3c37ecc608` |
| `ref.py 40 --mod 65521 --dump-r F --dump-all` | 224 680 | `6f29016e38d0737a95df0f0d338477eb94fc5fceb241edb5d8659419ef4bfbb8` |
| `ref.py 40 --mod 2097143 --dump-r F` | 224 680 | `53d428b30221bc2ace3b184f91a3536cc6fca8485aaddfa7349f8e9818b88e05` |
| `ref.py 60 --mod 65521 --dump-r F` | 1 117 509 | `3f6efe808d4301f792491e237cbeee9c2c0095f8dd7a7a5235e2ac5d76ed5341` |
| `ref.py 60 --mod 65521 --dump-r F --dump-all` | 1 117 520 | `a46ecc654f88468d9fa01d4e06b9c1159efd52fd0e03efa7abaa4f53182c66b1` |
| `ref.py 60 --mod 2097143 --dump-r F` | 1 117 520 | `3429b709a88a16334ecf303e3bf08c26a8428ebc36a7b042adc3114edd19dff6` |
| `ref.py 40 --dump-r F` (exact) | 224 680 | `7c5670fb5e129ff08cc77b8e476e7dc517cb73ca377a19459254e039343840a5` |
| `ref.py 60 --dump-r F` (exact) | 1 117 520 | `20174633ec4d90ff6c9504af9f753430200c8a91a59c3d06926a190bb85a42e2` |

With `--dump-all` the modulo-2097143 dumps do not change, since no entry
vanishes modulo 2097143.  The engine's `--dump-r` files at `N = 40` and
`N = 60` for both primes are byte-identical to the corresponding dumps
without `--dump-all` once their header line is removed
(`../engine/README.md`, §9).

## Cost

Single thread, PyPy 7.3.23 (Python 3.11.15) on aarch64:

| run | arithmetic | split multiply-adds | kernel (s) | empty-stack (s) | total (s) | peak RSS |
|---|---|---|---|---|---|---|
| `ref.py 40` | exact | 137 899 112 | 3.08 | 0.06 | 3.21 | 114.9 MiB |
| `ref.py 40 --mod 65521` | mod | 137 899 058 | 0.79 | 0.01 | 0.83 | 107.0 MiB |
| `ref.py 40 --mod 2097143` | mod | 137 899 112 | 0.78 | 0.01 | 0.82 | 107.5 MiB |
| `ref.py 60` | exact | 2 482 811 568 | 74-82 | 0.6-1.1 | 74.6-83.9 | 307.5 MiB |
| `ref.py 60 --mod 65521` | mod | 2 482 794 704 | 13.41 | 0.04 | 13.59 | 126.2 MiB |
| `ref.py 60 --mod 2097143` | mod | 2 482 811 568 | 13.37 | 0.04 | 13.55 | 124.5 MiB |
| `ref.py 100 --mod 2097143` | mod | 92 651 749 953 | 583.3 | 0.77 | 584.1 | 192.7 MiB |
| `ref.py 60 --support-check 60` | exact | 2 x 2 482 811 568 | 75.4 + 86.2 | | 162.2 | 336.9 MiB |

Throughput is 1.58-1.85e8 multiply-adds per second modulo a prime (16-bit
and 21-bit primes are indistinguishable) and 3.0-4.5e7 per second over the
integers (`a_60` has 200 bits, so the exact split multiplies integers of 3 to
4 limbs).  The empty-stack phase is negligible (166 749 990 multiply-adds,
0.77 s, at `N = 100`).  The executed split count equals the closed form of
`madd_count.py` in exact arithmetic; modulo `P` it is smaller by the products
skipped when a first factor vanishes (54 at `N = 40` and 16 864 at `N = 60`,
modulo 65521).

```
N        40         60         100        150         200         300
madds  1.379e8    2.483e9    9.265e10   1.619e12    1.227e13    2.120e14
```

At 1.6e8 multiply-adds per second this literal reference would take about
2.8 h per prime at `N = 150`, 21 h at `N = 200` and 15 days at `N = 300`, for
`N(N+1)(N^2+N+4)/12` stored entries (42.8 million, 134.7 million and
679.5 million).  It is a cross-check up to about `N = 100`-`150`, not a route
to `N = 300`; that is the purpose of the evaluation/interpolation engine.
The largest run is `N = 100` modulo 2097143 (584 s, 101 terms certified
against the data file); the exact mode was run up to `N = 60`.
