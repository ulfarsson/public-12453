# Exact coefficients of `Av(12453)` through length 150

Date: 28 August 2026

Let

\[
a_n=|\operatorname{Av}_n(12453)|,
\qquad A(x)=\sum_{n\geq0}a_nx^n.
\]

The file `av12453_terms_0_150.txt` contains the 151 exact integers
`a_0,...,a_150`.  In particular,

\[
\begin{split}
a_{150}={}&3822057739178404099007719791632020545156266830969175221131470523342088859240655328289587697088297741511203960758500758477699391695509589920898592073159171767612574.
\end{split}
\]

The SHA-256 digest of the coefficient file is

```text
f5ab4017ec65a661d8fbcd84d2f7893afe5e2c695dd082ace58399f7960340fc
```

## 1. Computation

The calculation evaluates the proved protected-tail stack recurrence for
`Av(12453)`.  It does not infer a recurrence from the coefficients.  The
compressed state table through weight 150 has 573,800 rows and 21,385,375
logical entries.  Its dominant split calculation performs exactly

\[
\binom{N}{3}+3\binom{N}{4}+6\binom{N}{5}
 +8\binom{N}{6}+4\binom{N}{7}
\]

modular multiply-adds, which is 1,294,425,854,905 at `N=150`.

`av12453_fast_rns.cpp` evaluates eight primes simultaneously in AVX-512
lanes, with five OpenMP row workers in the reported runs.  Residues were
computed as three separately restartable packs:

| pack | primes | kernel time | SHA-256 of checkpoint |
|---:|---:|---:|:---|
| 0 | 8 | 1750.559 s | `946c8f59850ae10d441384124d8cfcb78bd2a421602b250eb3ed225bc5eb48fd` |
| 1 | 8 | 1700.146 s | `e2565507a5c4b8ea9ae5cdd755af7b32500be4728793d671e58079fabe3bb859` |
| 2 | 8 | 1708.332 s | `12ec8b498ac113a4cf5edff5cda2f8ef626fb222ac4e13890aa85bf7ec633add` |

The timings are hardware-dependent.  The three packs can run independently;
they were checkpointed independently so an interruption loses at most one
pack.

## 2. Exact CRT certificate

Delete the left-to-right minima from a `12453`-avoider.  The remaining
permutation avoids `1342`: otherwise an earlier smaller entry, followed by an
occurrence of `1342`, would form

\[
1\oplus1342=12453.
\]

Writing `b_m=|Av_m(1342)|`, choosing the positions and values of the surviving
entries gives the injection bound

\[
a_n\leq B_n:=\sum_{m=0}^{n}\binom{n}{m}^{\!2}b_m.
\]

The exact `b_m` are generated from Bóna's algebraic series

\[
2(1+x)^3\sum_{m\geq0}b_mx^m
  =(1-8x)^{3/2}+1+20x-8x^2.
\]

At length 150 this gives

```text
B_150 =
491117992546644477348341426366753855073558214653738832717108692722198400291626497169873258856922645404659348774362096690472916866280789547280888767924431927918328676360
```

The product `M` of the first 18 computed 31-bit primes is

```text
M =
943488992924282437564976139623390751559982931846703874111095346030735777753929352180394298674234365882226430850047159265865336139703111059825484202366682940446185586511
```

Thus `M > B_150` (indeed `M/B_150 > 1.92`).  CRT reconstruction with those
18 primes therefore returns the unique possible integer coefficient at every
degree through 150.  This is a deterministic certificate, not a probabilistic
large-modulus assumption.

The remaining six 31-bit primes were withheld from reconstruction.  Every
reconstructed integer has the correct residue modulo each of them.

## 3. Independent verification

`av12453_scalar_residue_parallel.cpp` is a separately written scalar
implementation.  It uses 61-bit Montgomery arithmetic rather than the packed
32-bit reduction, parallelizes the recurrence stages differently, and does
not share the vector kernel.  At `N=150` it computed the full sequence modulo

\[
p=2^{61}-1=2305843009213693951
\]

in 1399.677 seconds.  All 151 reconstructed integers agree with this residue
sequence.  Its checkpoint digest is

```text
ff497e4e0a7100405a643f2e47fe8d018a66af84d8b16e3645aec63a4d5682ae
```

The new output also agrees exactly with the previously certified 101-term
file through `a_100`.

## 4. Reproduction

Build the packed program on an AVX-512 machine with GCC or Clang and OpenMP:

```sh
g++ -O3 -DNDEBUG -march=native -std=c++20 -fopenmp \
  av12453_fast_rns.cpp -o av12453_fast_rns
```

Evaluate the three packs.  The output path is written atomically.

```sh
for pack in 0 1 2; do
  ./av12453_fast_rns 150 --threads 5 --residues-only \
    --pack-index "$pack" \
    --output "av12453_residues_150_pack${pack}.txt"
done
```

For a from-scratch independent check, build and run the scalar implementation:

```sh
g++ -O3 -DNDEBUG -march=native -std=c++20 -fopenmp \
  av12453_scalar_residue_parallel.cpp \
  -o av12453_scalar_residue_parallel
./av12453_scalar_residue_parallel 150 --threads 8 \
  --prime 2305843009213693951 \
  --output av12453_residue_150_mersenne.txt
```

Finally, reconstruct from the first 18 moduli, certify the injection bound,
test the other six moduli and the independent scalar modulus, and compare the
old prefix:

```sh
python3 reconstruct_av12453_rns.py \
  av12453_residues_150_pack0.txt \
  av12453_residues_150_pack1.txt \
  av12453_residues_150_pack2.txt \
  --primary-count 18 \
  --independent-residue 2305843009213693951:av12453_residue_150_mersenne.txt \
  --known-prefix av12453_terms_0_100.txt \
  --output av12453_terms_0_150.txt
```

The expected summary is

```text
reconstructed=151 primary=18 redundant=6 independent=1 bound_bits=558 product_bits=558
```

`av12453_bound_certificate.cpp` is a small standalone audit of the exact
bound.  It independently prints `B_N` and enough primes below `2^62` for a
CRT product larger than the bound.

## 5. What the extra terms say about the generating function

No P-recursive or D-finite equation was found.  In particular, exact modular
rank calculations exclude every recurrence

\[
\sum_{j=0}^{r}p_j(n)a_{n+j}=0,
\qquad \deg p_j\leq d,
\]

valid from `n=0` whenever

\[
(r+1)(d+1)+r\leq151.
\]

The strongest positive signal is asymptotic.  Before the new calculation, the
terms only through 100 suggested

\[
a_n\sim C(9+4\sqrt2)^n
  \exp(-\kappa n^{1/3})n^{-17/4}
  \bigl(1+h n^{-1/3}+O(n^{-2/3})\bigr).
\]

Freezing the fit made on `70,...,100` and predicting all fifty unseen terms
`101,...,150` gives RMS relative error `2.45e-7` and maximum relative error
`4.13e-7`.  A refit on `70,...,150` gives

\[
\kappa=1.345509981,\qquad
C=0.827110923,\qquad
h=1.36798512.
\]

This remains conjectural, but the out-of-sample accuracy is strong evidence
for the `n^{1/3}` stretched exponential and against a regular-singular
power-law asymptotic.
