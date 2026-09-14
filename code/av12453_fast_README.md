# Fast exact computation of `Av(12453)`

`av12453_fast.cpp` evaluates the reduced protected-tail kernel recurrence for
the class `Av(12453)`.  It is an optimized implementation of
`av12453_reduced.py`, not a guessed recurrence.

## Build and run

```sh
g++ -O3 -DNDEBUG -march=native -std=c++20 -pthread \
  av12453_fast.cpp -o av12453_fast
./av12453_fast 100 --threads 7 --output data/av12453_terms_0_100.txt
```

The output has one line `n a_n` for every `0 <= n <= N`, so `N=100` produces
101 coefficients including `a_0`.  The default thread count is the number
reported by `std::thread::hardware_concurrency()`, capped by the number of
required primes.

## Exactness

Each worker evaluates the complete recurrence modulo a different prime just
below `2^61`, using Montgomery multiplication.  Workers are independent, so
thread scheduling cannot alter the result.  The program selects primes until
their product is greater than `2*15^N`, reconstructs by CRT, and chooses the
representative in `[0,M)`.

This is a proved reconstruction bound.  Deleting the left-to-right minima of
a `12453`-avoider leaves a `1342`-avoider.  If `b_m=|Av_m(1342)|`, Bóna's
generating function at `x=1/8` gives `b_m <= (32/27)8^m`.  Choosing the
positions and values of the surviving entries therefore gives

```text
|Av_n(12453)| <= sum_m C(n,m)^2 b_m
                <= (32/27)(1+sqrt(8))^(2n) < 2*15^n.
```

Thus the reconstructed coefficient is the unique exact integer, not a
probable reconstruction.  Seven 61-bit primes suffice at `N=100`.

The mathematical algorithm takes `O(N^7)` operations on exact integers.  In
this fixed-word realization, one full transfer is evaluated per modulus, so
one modulus costs `O(N^7)` 64-bit operations and the `Theta(N)` moduli needed
asymptotically cost `O(N^8)` in total.  The modulus runs are independent and
parallelize directly.  With `w` concurrent workers the kernel storage is
`O(w N^4)`; lower `--threads` if memory is the limiting resource.

The program has no third-party library dependency.  It requires a C++20
compiler with the widely supported `unsigned __int128` extension (GCC and
Clang provide it).  Its small big-integer class is used for the reconstruction
bound, modulus product, and final `N+1` CRT values; the large kernel table uses
64-bit modular words.

## The two storage reductions

The first-coordinate quotient is

```text
K_ell((p,q),(c,d)) = R_ell(p-c,q,d).
```

There is a further exact displacement law

```text
R_ell(a,q+1,d+1) = R_ell(a,q,d),       d >= a-1.
```

Consequently, for `a=0` only column `d=0` is stored, and for `a>0` only
columns `0,...,a-1` are stored.  The other entries are recovered in constant
time by

```text
R_ell(0,q,d) = R_ell(0,q-d,0)                    (0 <= d <= q),
R_ell(a,q,d) = R_ell(a,q-d+a-1,a-1)              (a>0, a <= d < a+q).
```

A short proof of the displacement law comes from induction in the reduced
kernel recurrence.  The two linear terms translate immediately (the extra
last-band term vanishes by support).  For a split, set its intermediate
coordinate to `m=n+1`.  Nonzero support forces exactly the inequalities needed
to apply the induction hypothesis to both factors.  Endpoint terms translate
as well.

The stored table through `N` therefore has

```text
N(N+1)(N^2+N+10)/24
```

64-bit entries: 4,254,625 at `N=100`.  The two nonsplit row sums are evaluated
by diagonal prefix scans.  The split remains order `N^7`; the exact number of
split multiply-adds per prime is

```text
C(N,3) + 3 C(N,4) + 6 C(N,5) + 8 C(N,6) + 4 C(N,7),
```

which is `74,030,312,895` at `N=100`.  The final empty-stack table uses a
further

```text
C(N,2) + 3 C(N,3) + 4 C(N,4) + 2 C(N,5)
```

products (`166,749,990` at `N=100`).  The progress log reports the two counts
separately.

## Independent checks

`av12453_dense_mod_verify.cpp` is a deliberately separate verifier.  It
stores every endpoint, evaluates the reduced recurrence literally, uses no
second-coordinate displacement law and no prefix scans, and works modulo the
Mersenne prime `2^61-1`.

```sh
g++ -O3 -DNDEBUG -march=native -std=c++20 \
  av12453_dense_mod_verify.cpp -o av12453_dense_mod_verify
./av12453_dense_mod_verify 60 > dense_residues_60.txt
```

The optimized exact output agrees with the existing file through `n=45`.  The
dense verifier independently checks the second-coordinate compression and
prefix-scan optimizations: it agrees modulo `2^61-1` through `n=60`.
The final seven-prime series through `n=100` is byte-for-byte identical to a
redundant nine-prime run.  Its SHA-256 digest is

```text
1e83f2cb73f307579502f0e9c0982a1e749ec6e6f89d77469f5c13950ce4b2dd
```

## Benchmarks

These runs used GCC 13.3.0 with the build command above in a nine-vCPU Linux
container on an AMD EPYC 9V74 processor.  There was one worker per modulus.
Times are the program's elapsed timer for all parallel modular transfers and
CRT reconstruction; they are hardware dependent.

| N | primes | stored entries per prime | elapsed |
|---:|---:|---:|---:|
| 30 | 2 | 36,425 | 0.106 s |
| 40 | 3 | 112,750 | 0.910 s |
| 50 | 4 | 272,000 | 3.899 s |
| 60 | 4 | 559,675 | 13.236 s |
| 100 | 7 | 4,254,625 | 646.980 s |

The `N=100` run had peak resident memory 250,688 KiB (about 245 MiB).

For comparison, the older full-kernel exact C++ program took about 34.4
seconds already at `N=40` in the same container.
