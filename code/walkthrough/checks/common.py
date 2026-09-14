"""Shared brute-force helpers for the exhaustive checks of the paper's statements.

Everything here is elementary and independent of the paper's recurrences:
permutations come from permuta (Perm, Av), and all other functions are direct
transcriptions of definitions.  Paper notation is 1-based; permuta is 0-based,
so `P` and `word` convert.

Run with the PyPy virtual environment:  pypy3
"""
from itertools import combinations, permutations
from permuta import Perm, Av

# ----------------------------------------------------------- conversions
def word(s):
    """Tuple of ints from an int tuple/list or a string like '9 11 10 14 5' or '12453'."""
    if isinstance(s, str):
        parts = s.split()
        return tuple(int(x) for x in (parts if len(parts) > 1 else s))
    return tuple(int(v) for v in s)

def P(s):
    """permuta Perm (0-based) from 1-based data."""
    w = word(s)
    assert sorted(w) == list(range(1, len(w) + 1)), "not a permutation of 1..n"
    return Perm(tuple(v - 1 for v in w))

def one_based(perm):
    return tuple(v + 1 for v in perm)

def std(w):
    """Standardization: relabel the distinct entries of w by 1..len(w)."""
    r = {v: i + 1 for i, v in enumerate(sorted(w))}
    return tuple(r[v] for v in w)

def restrict(w, X):
    """Subword of w on the value set X (paper: w|_X)."""
    X = set(X)
    return tuple(v for v in w if v in X)

# ------------------------------------------------------------- patterns
def iota(d):
    return tuple(range(1, d + 1))

def oplus(a, b):
    a, b = word(a), word(b)
    return a + tuple(v + len(a) for v in b)

def beta(d):
    """beta_d = iota_d (+) 231 as a 1-based tuple; beta(1) = 1342, beta(2) = 12453."""
    return oplus(iota(d), (2, 3, 1))

def contains(w, pat):
    """Classical containment of the pattern pat (1-based tuple) in the word w."""
    w, pat = word(w), word(pat)
    k = len(pat)
    for idx in combinations(range(len(w)), k):
        if std(tuple(w[i] for i in idx)) == pat:
            return True
    return False

def avoids(w, pat):
    return not contains(w, pat)

def avoiders(n, pat):
    """All 1-based avoiders of length n, from permuta's Av."""
    pat = word(pat)
    return [one_based(p) for p in Av([Perm(tuple(v - 1 for v in pat))]).of_length(n)]

def all_perms(n):
    return list(permutations(range(1, n + 1)))

# ------------------------------------------------------ triggers, obligations
def lis_ending(w):
    """lis_ending(w)[i] = length of the longest increasing subsequence ending at position i."""
    w = word(w)
    out = []
    for i, v in enumerate(w):
        best = 1
        for j in range(i):
            if w[j] < v and out[j] + 1 > best:
                best = out[j] + 1
        out.append(best)
    return out

def trigger_positions(w, d):
    """Positions j (0-based) whose entry ends an increasing d-subsequence (the d-triggers)."""
    L = lis_ending(w)
    return [j for j, l in enumerate(L) if l >= d]

def projection(w, j):
    """The word after position j restricted to values above w[j] (paper: pi_{j+1}...pi_n|_{x > pi_j})."""
    w = word(w)
    return tuple(v for v in w[j + 1:] if v > w[j])

def prefixes_of_avoiders(n, pat):
    """Set of all proper prefixes (as tuples) of avoiders of length n."""
    out = set()
    for p in avoiders(n, pat):
        for k in range(0, n):
            out.add(p[:k])
    return out

def completions(prefix, n, pat):
    """All words w on the unread letters with prefix.w an avoider of length n."""
    prefix = word(prefix)
    unread = [v for v in range(1, n + 1) if v not in prefix]
    return [w for w in permutations(unread) if avoids(prefix + w, pat)]

def fibonacci(n):
    a, b = 1, 1
    for _ in range(n - 1):
        a, b = b, a + b
    return a
