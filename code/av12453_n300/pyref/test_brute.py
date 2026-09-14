"""Independent validation of the containment test used by ref.py --brute.

(1) |Av_n(231)| = Catalan numbers.
(2) |Av_n(1342)| = 1,1,2,6,23,103,512,2740 (Bona / OEIS A022558).
(3) |Av_n(12345)| computed by RSK (sum of (f^lambda)^2 over shapes with at
    most 4 rows, hook-length formula) -- an entirely different method -- and
    compared with the same brute force.  At n = 7 it separates 12345 (4550)
    from 12453 (4581), so the test is not merely counting 'contains an
    increasing 5-subsequence'.
"""
import sys
from math import factorial
from ref import brute_counts

def partitions(n, maxpart=None):
    if maxpart is None: maxpart = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest

def fdim(lam):
    n = sum(lam)
    conj = [sum(1 for r in lam if r > j) for j in range(lam[0])]
    prod = 1
    for i, r in enumerate(lam):
        for j in range(r):
            prod *= (r - j) + (conj[j] - i) - 1     # hook length
    return factorial(n) // prod

def av_increasing(n, k):
    """|Av_n(12...k)| = sum of (f^lambda)^2 over lambda |- n with < k rows."""
    return sum(fdim(l) ** 2 for l in partitions(n) if len(l) <= k - 1) if n else 1

ok = True
cat = [1, 1, 2, 5, 14, 42, 132]
got = brute_counts(6, (2, 3, 1))
print("Av(231) :", got, "==", cat, "OK" if got == cat else "FAIL"); ok &= got == cat

a1342 = [1, 1, 2, 6, 23, 103, 512, 2740]
got2 = brute_counts(7, (1, 3, 4, 2))
print("Av(1342):", got2, "==", a1342, "OK" if got2 == a1342 else "FAIL"); ok &= got2 == a1342

exp = [av_increasing(n, 5) for n in range(8)]
got3 = brute_counts(7, (1, 2, 3, 4, 5))
print("Av(12345):", got3, "== RSK", exp, "OK" if got3 == exp else "FAIL"); ok &= got3 == exp

got4 = brute_counts(7, (1, 2, 4, 5, 3))
print("Av(12453):", got4, " (differs from Av(12345) at n=7: %d vs %d)" % (got4[7], exp[7]))
ok &= got4[7] != exp[7]
sys.exit(0 if ok else 1)
