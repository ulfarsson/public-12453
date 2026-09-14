"""Exhaustive checks for Sections 6-8, Section 10, and the finite content of
Theorem 1.1 of ``paper/av12453_polytime.tex``.

Every check compares an object built from the paper's displayed formulas with
an object built by brute force from the definitions (permuta avoiders, or an
explicit enumeration of the paths of the literal recurrence graph
\\eqref{eq:H}).  Nothing here imports the reference implementations in
``code/``; all formulas below are transcribed from the paper.

Run with PyPy:

    pypy3 code/walkthrough/checks/sec678.py
"""
from __future__ import annotations

import os
import sys
import time
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, permutations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from checks import common as C  # noqa: E402

REPO = os.path.dirname(  # .../repo
    os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

# ======================================================================
# Brute force side: avoider counts from permuta
# ======================================================================

_AVOID_COUNT = {}


def avoider_count(n, pat):
    """|Av_n(pat)| from permuta (brute force from the definition)."""
    key = (n, tuple(pat))
    if key not in _AVOID_COUNT:
        _AVOID_COUNT[key] = len(C.avoiders(n, pat))
    return _AVOID_COUNT[key]


# ======================================================================
# Transcriptions of the paper's displayed formulas
# ======================================================================

def T(i, h, p):
    """eq:T -- T_{i,h}(p) = (p_0,...,p_{i-1}, h, p_{i+1}+p_i-1-h, p_{i+2},...)."""
    q = list(p)
    q[i + 1] = p[i + 1] + p[i] - 1 - h
    q[i] = h
    return tuple(q)


def U(h, p):
    """eq:U -- U_h(p) = (p_0,...,p_{d-2},h);  delta_h = p_{d-1}-1-h."""
    return tuple(p[:-1]) + (h,)


def nz(L):
    """Drop the zero parts of a composition."""
    return tuple(x for x in L if x)


def controls(d, m):
    """All p in N^d with ||p||_1 = m."""
    if d == 1:
        return [(m,)]
    out = []
    for first in range(m + 1):
        for rest in controls(d - 1, m - first):
            out.append((first,) + rest)
    return out


# ---------------------------------------------------------------- eq:H
_H_MEMO = {}


def H(d, p, L):
    """eq:H together with eq:initial-terminal: the literal recurrence.

    H_p(L) is defined in the paper as the number of beta_d-avoiding
    completions of a legal prefix with state (p,L); this function is the
    paper's recurrence for it, used here only as *the* recurrence whose
    labelled paths the kernels count.
    """
    p = tuple(p)
    L = tuple(L)
    key = (d, p, L)
    if key in _H_MEMO:
        return _H_MEMO[key]
    if not any(p) and not L:
        _H_MEMO[key] = 1
        return 1
    tot = 0
    for i in range(d - 1):
        for h in range(p[i]):
            tot += H(d, T(i, h, p), L)
    for h in range(p[d - 1]):
        delta = p[d - 1] - 1 - h
        if L:
            newL = nz((L[0] + delta,) + L[1:])
        else:
            newL = nz((delta,))
        tot += H(d, U(h, p), newL)
    if L:
        l1 = L[0]
        tot += min(2, l1) * H(d, p, nz((l1 - 1,) + L[1:]))
        for j in range(2, l1):
            tot += H(d, p, (j - 1, l1 - j) + L[1:])
    _H_MEMO[key] = tot
    return tot


# ------------------------------------------------------- eq:K and eq:G
def kernel_table(d, N):
    """eq:K (prop:kernel-recurrence): K_ell(p,.) for every ell>=1, p in N^d
    with ||p||_1 + ell <= N.  Returned as {(ell,p): {t: value}}."""
    K = {}
    for w in range(1, N + 1):
        for ell in range(1, w + 1):
            for p in controls(d, w - ell):
                row = defaultdict(int)
                for i in range(d - 1):                       # early-band moves
                    for h in range(p[i]):
                        for t, v in K[(ell, T(i, h, p))].items():
                            row[t] += v
                for h in range(p[d - 1]):                    # last-band moves
                    delta = p[d - 1] - 1 - h
                    for t, v in K[(ell + delta, U(h, p))].items():
                        row[t] += v
                if ell == 1:                                 # eq:D
                    row[p] += 1
                else:
                    for t, v in K[(ell - 1, p)].items():
                        row[t] += 2 * v
                for a in range(1, ell - 1):                  # split convolution
                    b = ell - 1 - a
                    for u, va in K[(a, p)].items():
                        for t, vb in K[(b, u)].items():
                            row[t] += va * vb
                K[(ell, p)] = {t: v for t, v in row.items() if v}
    return K


def empty_stack_table(d, N, K):
    """eq:G (cor:empty-stack-recurrence), with K_0 the identity kernel."""
    G = {}
    zero = tuple([0] * d)
    for m in range(N + 1):
        for p in controls(d, m):
            tot = 1 if p == zero else 0
            for i in range(d - 1):
                for h in range(p[i]):
                    tot += G[T(i, h, p)]
            for h in range(p[d - 1]):
                delta = p[d - 1] - 1 - h
                src = U(h, p)
                if delta == 0:
                    tot += G[src]                     # K_0 = identity
                else:
                    for t, v in K[(delta, src)].items():
                        tot += v * G[t]
            G[p] = tot
    return G


def family_counts(d, N):
    """eq:answer-G -- a_n^{(d)} = G_{(n,0,...,0)} from the eq:K/eq:G algorithm."""
    K = kernel_table(d, N)
    G = empty_stack_table(d, N, K)
    return [G[(n,) + tuple([0] * (d - 1))] for n in range(N + 1)]


# ======================================================================
# Brute force side: paths of the literal recurrence graph eq:H
# ======================================================================
#
# A kernel state is (p, M) where M lists the block sizes *before* the marked
# tail.  The moves are exactly the four groups of eq:H, acting on the blocks
# before the marker; the path stops when M is empty (the tail is exposed) and
# reports the control reached there.  K_ell(p,t) is by definition
# (cor:protected-tail) the number of such labelled paths with terminal
# control t.

def _moves(d, p, M):
    """Labelled successors (p',M') of (p,M), one entry per labelled transition."""
    out = []
    for i in range(d - 1):
        for h in range(p[i]):
            out.append((T(i, h, p), M))
    for h in range(p[d - 1]):
        delta = p[d - 1] - 1 - h
        out.append((U(h, p), nz((M[0] + delta,) + M[1:])))
    for _ in range(min(2, M[0])):
        out.append((p, nz((M[0] - 1,) + M[1:])))
    for j in range(2, M[0]):
        out.append((p, (j - 1, M[0] - j) + M[1:]))
    return out


_PATH_MEMO = {}


def stopped_paths(d, p, M):
    """{t: number of labelled paths from (p,M) stopped at the first exposure}."""
    key = (d, p, M)
    if key in _PATH_MEMO:
        return _PATH_MEMO[key]
    if not M:
        res = {p: 1}
    else:
        res = defaultdict(int)
        for p2, M2 in _moves(d, p, M):
            for t, v in stopped_paths(d, p2, M2).items():
                res[t] += v
        res = dict(res)
    _PATH_MEMO[key] = res
    return res


def stopped_paths_enumerated(d, p, M):
    """Same count, by explicit depth-first enumeration of the paths themselves
    (no memoization: every path is walked separately)."""
    res = defaultdict(int)
    stack = [(p, M)]
    while stack:
        p0, M0 = stack.pop()
        if not M0:
            res[p0] += 1
            continue
        stack.extend(_moves(d, p0, M0))
    return dict(res)


def bf_kernels(d, N):
    """Brute-force kernel table {(ell,p): {t: paths}} for all grades <= N."""
    out = {}
    for w in range(1, N + 1):
        for ell in range(1, w + 1):
            for p in controls(d, w - ell):
                out[(ell, p)] = stopped_paths(d, p, (ell,))
    return out


# ======================================================================
# Section 7: the reduced (first-coordinate quotient) recurrence
# ======================================================================

def reduced_table(N):
    """eq:R-recurrence -- R_{ell,a}(q,s) for ell>=1, a,q>=0, ell+a+q <= N.
    Returned as {(ell,a,q): {s: value}}."""
    R = {}
    for w in range(1, N + 1):
        for ell in range(1, w + 1):
            for a in range(w - ell + 1):
                q = w - ell - a
                row = defaultdict(int)
                for h in range(a):                       # early-band moves
                    for s, v in R[(ell, h, a + q - h - 1)].items():
                        row[s] += v
                for r in range(q):                       # last-band moves
                    for s, v in R[(ell + q - r - 1, a, r)].items():
                        row[s] += v
                if ell == 1:                             # D_{1,a}(q,s)
                    if a == 0:
                        row[q] += 1
                else:                                    # D_{ell,a} = 2 R_{ell-1,a}
                    for s, v in R[(ell - 1, a, q)].items():
                        row[s] += 2 * v
                for l1 in range(1, ell - 1):             # split convolution
                    l2 = ell - 1 - l1
                    for a1 in range(a + 1):
                        a2 = a - a1
                        for m, v1 in R[(l1, a1, q)].items():
                            for s, v2 in R[(l2, a2, m)].items():
                                row[s] += v1 * v2
                R[(ell, a, q)] = {s: v for s, v in row.items() if v}
    return R


def reduced_counts(N):
    """|Av_n(12453)| for n <= N from the Section 7 reduced recurrence: eq:G with
    every kernel entry K_ell((p,q),(u,v)) replaced by R_{ell,p-u}(q,v)
    (lem:d2-translation)."""
    R = reduced_table(N)
    G = {}
    for m in range(N + 1):
        for p in range(m + 1):
            q = m - p
            tot = 1 if (p, q) == (0, 0) else 0
            for h in range(p):                      # early band: T_{0,h}((p,q))
                tot += G[(h, q + p - 1 - h)]
            for r in range(q):                      # last band, delta = q-1-r
                delta = q - 1 - r
                if delta == 0:
                    tot += G[(p, r)]                # K_0 = identity
                else:
                    for u in range(p + 1):
                        for s, v in R[(delta, p - u, r)].items():
                            tot += v * G[(u, s)]
            G[(p, q)] = tot
    return [G[(n, 0)] for n in range(N + 1)]


def reduced_counts_stored_only(N):
    """The same numbers, but reading every reduced entry out of the storage
    scheme retained after lem:d2-second-translation: only s=0 is stored when
    a=0, and only 0<=s<a when a>=1; the omitted entries are recovered from
    eq:d2-second-translation."""
    R = reduced_table(N)
    stored = {}
    for (ell, a, q), row in R.items():
        keep = {}
        if a == 0:
            if row.get(0):
                keep[0] = row[0]
        else:
            for s in range(a):
                if row.get(s):
                    keep[s] = row[s]
        stored[(ell, a, q)] = keep

    def entry(ell, a, q, s):
        """R_{ell,a}(q,s) from the retained entries only."""
        if a == 0:
            if s > q:
                return 0
            return stored[(ell, 0, q - s)].get(0, 0)     # R_{l,0}(q,s)=R_{l,0}(q-s,0)
        if s < a:
            return stored[(ell, a, q)].get(s, 0)
        if s > a + q - 1:
            return 0
        return stored[(ell, a, q - s + a - 1)].get(a - 1, 0)

    G = {}
    for m in range(N + 1):
        for p in range(m + 1):
            q = m - p
            tot = 1 if (p, q) == (0, 0) else 0
            for h in range(p):
                tot += G[(h, q + p - 1 - h)]
            for r in range(q):
                delta = q - 1 - r
                if delta == 0:
                    tot += G[(p, r)]
                else:
                    for u in range(p + 1):
                        for s in range(0, (p - u) + r + 1):
                            v = entry(delta, p - u, r, s)
                            if v:
                                tot += v * G[(u, s)]
            G[(p, q)] = tot
    return [G[(n, 0)] for n in range(N + 1)]


# ======================================================================
# Section 8.2: the recursive method on the literal recurrence eq:H
# ======================================================================

def _sampler_moves(bands, stack):
    """The legal letters from a concrete configuration, with the resulting
    configuration, exactly as in prop:state-invariant(b): a value of B_i with
    i<d-1 (non-trigger move), a value of B_{d-1} (merger), a value of I_1
    (split).  Returns a list of (letter, bands', stack')."""
    d = len(bands)
    out = []
    for i in range(d - 1):
        B = bands[i]
        for h, x in enumerate(B):
            nb = list(bands)
            nb[i] = B[:h]
            nb[i + 1] = tuple(sorted(B[h + 1:] + bands[i + 1]))
            out.append((x, tuple(nb), stack))
    B = bands[d - 1]
    for h, x in enumerate(B):
        nb = list(bands)
        nb[d - 1] = B[:h]
        head = tuple(sorted(B[h + 1:] + (stack[0] if stack else ())))
        rest = stack[1:] if stack else ()
        ns = ((head,) if head else ()) + rest
        out.append((x, tuple(nb), ns))
    if stack:
        I1 = stack[0]
        for r, x in enumerate(I1, start=1):
            lower, upper = I1[:r - 1], I1[r:]
            ns = tuple(b for b in (lower, upper) if b) + stack[1:]
            out.append((x, bands, ns))
    return out


def sampler_distribution(n, d=2):
    """Enumerate every complete path of eq:H from H_{(n,0,...,0)}(empty),
    assigning each transition the probability (summand value)/(state value) of
    the recursive method.

    Returns (dist, nodes, mismatch) where dist maps the permutation read off a
    path to its exact Fraction probability, nodes is the number of states
    visited, and mismatch is None or a state at which the recurrence value
    H_p(L) differs from the number of avoiding completions actually below that
    state (the leaves of its subtree), which is the quantity the recursive
    method requires it to be.
    """
    bands = (tuple(range(1, n + 1)),) + ((),) * (d - 1)
    out = {}
    stats = {"nodes": 0, "mismatch": None}

    def walk(bands, stack, word, prob):
        """Returns the number of complete paths below this state."""
        stats["nodes"] += 1
        p = tuple(len(b) for b in bands)
        L = tuple(len(b) for b in stack)
        total = H(d, p, L)
        if not any(p) and not L:
            out[tuple(word)] = out.get(tuple(word), Fraction(0)) + prob
            leaves = 1
        else:
            leaves = 0
            for x, nb, ns in _sampler_moves(bands, stack):
                np_ = tuple(len(b) for b in nb)
                nL = tuple(len(b) for b in ns)
                leaves += walk(nb, ns, word + [x],
                               prob * Fraction(H(d, np_, nL), total))
        if leaves != total and stats["mismatch"] is None:
            stats["mismatch"] = (tuple(word), p, L, total, leaves)
        return leaves

    walk(bands, (), [], Fraction(1))
    return out, stats["nodes"], stats["mismatch"]


# ======================================================================
# Section 10: the Wilf class of 12453
# ======================================================================

def dihedral_orbit(pat):
    """Closure of pat under reverse, complement and inverse (1-based tuples)."""
    def rev(w):
        return tuple(reversed(w))

    def comp(w):
        k = len(w)
        return tuple(k + 1 - v for v in w)

    def inv(w):
        k = len(w)
        out = [0] * k
        for i, v in enumerate(w, start=1):
            out[v - 1] = i
        return tuple(out)

    seen = {tuple(pat)}
    frontier = [tuple(pat)]
    while frontier:
        w = frontier.pop()
        for f in (rev, comp, inv):
            z = f(w)
            if z not in seen:
                seen.add(z)
                frontier.append(z)
    return seen


def s5_avoider_counts(nmax):
    """{pattern: [|Av_0(pattern)|,...,|Av_nmax(pattern)|]} for every pattern in
    S_5, by brute force: for each permutation of [n], list the length-5
    patterns it contains."""
    pats = [tuple(p) for p in permutations(range(1, 6))]
    counts = {p: [] for p in pats}
    for n in range(nmax + 1):
        if n < 5:
            for p in pats:
                counts[p].append(_factorial(n))
            continue
        contains = defaultdict(int)
        idxs = list(combinations(range(n), 5))
        for w in permutations(range(1, n + 1)):
            seen = set()
            for idx in idxs:
                seen.add(C.std((w[idx[0]], w[idx[1]], w[idx[2]], w[idx[3]], w[idx[4]])))
            for s in seen:
                contains[s] += 1
        for p in pats:
            counts[p].append(_factorial(n) - contains[p])
    return counts


def _factorial(n):
    r = 1
    for i in range(2, n + 1):
        r *= i
    return r



# ======================================================================
# Section 8.1 helpers: Bona's 1342 generating function and the CRT bound
# ======================================================================

def bona_1342(N):
    """eq:bona-1342 -- the coefficients of
        ((1-8x)^{3/2} - 8x^2 + 20x + 1) / (2(1+x)^3)
    expanded with exact rational arithmetic."""
    num = [Fraction(0)] * (N + 1)
    c = Fraction(1)
    for k in range(N + 1):
        num[k] += c * Fraction((-8) ** k)
        c = c * (Fraction(3, 2) - k) / (k + 1)
    num[0] += 1
    if N >= 1:
        num[1] += 20
    if N >= 2:
        num[2] += -8
    den = [Fraction(2), Fraction(6), Fraction(6), Fraction(2)]
    b = []
    for n in range(N + 1):
        acc = num[n]
        for j in range(1, min(4, n + 1)):
            acc -= den[j] * b[n - j]
        b.append(acc / den[0])
    out = []
    for n, v in enumerate(b):
        if v.denominator != 1:
            raise ValueError("eq:bona-1342 coefficient %d is not an integer" % n)
        out.append(int(v))
    return out


def crt_bound(N, b):
    """eq:exact-crt-bound -- B_N = sum_m binom(N,m)^2 b_m."""
    return sum(_binom(N, m) ** 2 * b[m] for m in range(N + 1))


def largest_primes_below(bound, count):
    """The `count` largest primes below `bound`, decreasing."""
    def is_prime(n):
        if n < 2 or n % 2 == 0:
            return n == 2
        i = 3
        while i * i <= n:
            if n % i == 0:
                return False
            i += 2
        return True

    out = []
    x = bound - 1
    while len(out) < count:
        if is_prime(x):
            out.append(x)
        x -= 1
    return out


def delete_lr_minima(w):
    """Standardization of w with its left-to-right minima deleted."""
    best = None
    kept = []
    for v in w:
        if best is None or v < best:
            best = v
        else:
            kept.append(v)
    return C.std(tuple(kept))


# ======================================================================
# The checks
# ======================================================================

def check_lem_support(nmax, verbose=False):
    """Lemma 6.1 (lem:support).

    "For every ell >= 1,
       supp K_ell(p,.) subseteq {p} u {t : ||t||_1 <= ||p||_1 - 1}."  (eq:support)

    Compared: the kernel table computed from the paper's kernel recurrence
    eq:K, for d = 1, 2, 3 and every grade ||p||_1+ell <= 12 (d <= 2) or <= 10
    (d = 3), against (a) the stated support region -- every entry outside it
    must be zero -- and (b) the brute-force count of stopped paths in the
    literal recurrence graph eq:H, which is the definition of K_ell(p,t)
    (cor:protected-tail).  The brute-force counts are produced both by a
    memoized path count and, for grades <= 8, by an explicit depth-first
    enumeration of every single path (544474 paths at grade 8 for d = 2).  Also checked: the bound
    1 + binom(||p||_1+d-1, d) on the number of terminal controls of a row,
    used in the complexity count of Section 6; and, since the brute force runs
    in the graph of eq:H, that eq:H reproduces |Av_n(beta_d)| for d = 1, 2, 3
    and n <= nmax.
    """
    t0 = time.time()
    checks = 0
    detail_bits = []
    # the graph used for the brute force is the graph of eq:H; check first that
    # its complete paths count the avoiders, for every d used below
    for d in (1, 2, 3):
        for n in range(nmax + 1):
            checks += 1
            got = H(d, (n,) + tuple([0] * (d - 1)), ())
            want = avoider_count(n, C.beta(d))
            if got != want:
                return dict(ok=False, checks=checks, seconds=time.time() - t0,
                            detail="eq:H gives H_{(%d,0..)}(empty) = %d for d=%d, "
                                   "permuta gives %d" % (n, got, d, want))
    for d, W in ((1, 12), (2, 12), (3, 10)):
        K = kernel_table(d, W)
        BF = bf_kernels(d, W)

        for (ell, p), row in BF.items():
            if ell + sum(p) <= 8:
                got = stopped_paths_enumerated(d, p, (ell,))
                checks += 1
                if {t: v for t, v in got.items() if v} != {t: v for t, v in row.items() if v}:
                    return dict(ok=False, checks=checks, seconds=time.time() - t0,
                                detail="d=%d: explicit path enumeration != memoized "
                                       "path count at K_%d(%s,.)" % (d, ell, p))

        for key, row in BF.items():
            checks += 1
            if {t: v for t, v in K[key].items() if v} != {t: v for t, v in row.items() if v}:
                ell, p = key
                return dict(ok=False, checks=checks, seconds=time.time() - t0,
                            detail="d=%d: eq:K row != stopped-path count at "
                                   "K_%d(%s,.): %s vs %s" % (d, ell, p, K[key], row))

        for (ell, p), row in BF.items():
            mass = sum(p)
            for t in [tt for m in range(W + 1) for tt in controls(d, m)]:
                inside = (t == p) or (sum(t) <= mass - 1)
                checks += 1
                if row.get(t, 0) and not inside:
                    return dict(ok=False, checks=checks, seconds=time.time() - t0,
                                detail="d=%d: K_%d(%s,%s) = %d is nonzero outside "
                                       "eq:support" % (d, ell, p, t, row[t]))
            checks += 1
            if len([1 for v in row.values() if v]) > 1 + _binom(mass + d - 1, d):
                return dict(ok=False, checks=checks, seconds=time.time() - t0,
                            detail="d=%d: row K_%d(%s,.) has more than "
                                   "1+binom(||p||+d-1,d) terminal controls"
                                   % (d, ell, p))
        detail_bits.append("d=%d: %d rows of grade <= %d" % (d, len(BF), W))
    return dict(ok=True, checks=checks, seconds=time.time() - t0,
                detail="eq:K rows agree with brute-force stopped-path counts "
                       "(and with explicit path enumeration for grade <= 8), "
                       "every nonzero entry lies in {p} u {||t||<=||p||-1}, and "
                       "eq:H itself reproduces |Av_n(beta_d)| for n <= %d; "
                       % nmax + "; ".join(detail_bits))


def check_d2_exact_support(nmax, verbose=False):
    """Lemma 7.1 (lem:d2-exact-support).

    "supp K_ell((p,q),.) = {(p,q)} u {(u,v): 0<=u<=p, v>=0, u+v <= p+q-1}."

    Compared: the exact support of the brute-force kernel rows (stopped paths
    of the literal recurrence graph eq:H) with the stated set, entry by entry
    over the full box of terminal controls, for every grade ell+p+q <= 12.
    """
    t0 = time.time()
    W = 12
    BF = bf_kernels(2, W)
    checks = 0
    for (ell, pq), row in BF.items():
        p, q = pq
        for u in range(W + 1):
            for v in range(W + 1 - u):
                t = (u, v)
                stated = (t == pq) or (u <= p and u + v <= p + q - 1)
                actual = bool(row.get(t, 0))
                checks += 1
                if stated != actual:
                    return dict(ok=False, checks=checks, seconds=time.time() - t0,
                                detail="K_%d(%s,%s): stated support %s, actual %s"
                                       % (ell, pq, t, stated, actual))
    return dict(ok=True, checks=checks, seconds=time.time() - t0,
                detail="exact support of every brute-force kernel row of grade "
                       "<= %d equals eq:support-d2 (%d rows)" % (W, len(BF)))


def check_d2_translation(nmax, verbose=False):
    """Lemma 7.2 (lem:d2-translation) and the definition eq:R-definition.

    "For ell >= 1 and 0 <= c <= p,  K_ell((p,q),(c,s)) = K_ell((p-c,q),(0,s))."
    "R_{ell,a}(q,s) := K_ell((a,q),(0,s))."

    Compared: (a) the translation identity, entry by entry, on the brute-force
    kernel table (stopped-path counts in the graph of eq:H) for all grades
    <= 12 -- both sides are path counts of genuinely different graphs, so this
    tests the lemma and not an algebraic rearrangement; (b) the reduced table
    R computed from the Section 7 recurrence eq:R-recurrence against the
    brute-force value of K_ell((a,q),(0,s)), entry by entry, for all grades
    <= 12.
    """
    t0 = time.time()
    W = 12
    BF = bf_kernels(2, W)
    R = reduced_table(W)
    checks = 0
    # (a) translation identity on the brute-force table
    for (ell, pq), row in BF.items():
        p, q = pq
        for c in range(p + 1):
            src = BF[(ell, (p - c, q))]
            for s in range(W + 1):
                lhs = row.get((c, s), 0)
                rhs = src.get((0, s), 0)
                checks += 1
                if lhs != rhs:
                    return dict(ok=False, checks=checks, seconds=time.time() - t0,
                                detail="K_%d((%d,%d),(%d,%d))=%d but K_%d((%d,%d),(0,%d))=%d"
                                       % (ell, p, q, c, s, lhs, ell, p - c, q, s, rhs))
    # (b) eq:R-recurrence reproduces the brute-force reduced entries
    for (ell, a, q), row in R.items():
        bf = BF[(ell, (a, q))]
        for s in range(W + 1):
            checks += 1
            if row.get(s, 0) != bf.get((0, s), 0):
                return dict(ok=False, checks=checks, seconds=time.time() - t0,
                            detail="R_{%d,%d}(%d,%d)=%d but brute-force "
                                   "K_%d((%d,%d),(0,%d))=%d" % (
                                       ell, a, q, s, row.get(s, 0), ell, a, q, s,
                                       bf.get((0, s), 0)))
    return dict(ok=True, checks=checks, seconds=time.time() - t0,
                detail="translation identity holds for every (ell,p,q,c,s) of "
                       "grade <= %d on the brute-force kernel table, and "
                       "eq:R-recurrence reproduces every brute-force reduced "
                       "entry" % W)


def check_d2_second_translation(nmax, verbose=False):
    """Lemma 7.3 (lem:d2-second-translation).

    "For ell >= 1 and a,q,s >= 0, whenever s >= a-1,
        R_{ell,a}(q+1,s+1) = R_{ell,a}(q,s)."
    and the remark "The hypothesis s >= a-1 cannot be weakened: ...
    R_{1,2}(1,1)=3 but R_{1,2}(0,0)=2."

    Compared: both sides are read off the brute-force kernel table, i.e.
    R_{ell,a}(q,s) = K_ell((a,q),(0,s)) counted by explicit stopped paths in
    the graph of eq:H, for every (ell,a,q,s) with s >= a-1 and both grades
    <= 12.  The sharpness remark is checked against the same brute-force values,
    and we also record for which (ell,a,q,s) with s < a-1 the identity fails.
    """
    t0 = time.time()
    W = 12
    BF = bf_kernels(2, W)

    def Rv(ell, a, q, s):
        return BF[(ell, (a, q))].get((0, s), 0)

    checks = 0
    nontrivial = [0]
    for (ell, aq) in sorted(BF):
        a, q = aq
        if ell + a + q + 1 > W:
            continue
        for s in range(max(0, a - 1), W + 1):
            checks += 1
            if Rv(ell, a, q, s):
                nontrivial[0] += 1
            if Rv(ell, a, q + 1, s + 1) != Rv(ell, a, q, s):
                return dict(ok=False, checks=checks, seconds=time.time() - t0,
                            detail="R_{%d,%d}(%d,%d)=%d != R_{%d,%d}(%d,%d)=%d"
                                   % (ell, a, q + 1, s + 1, Rv(ell, a, q + 1, s + 1),
                                      ell, a, q, s, Rv(ell, a, q, s)))
    # sharpness
    checks += 2
    sharp = (Rv(1, 2, 1, 1), Rv(1, 2, 0, 0))
    if sharp != (3, 2):
        return dict(ok=False, checks=checks, seconds=time.time() - t0,
                    detail="paper's sharpness example: R_{1,2}(1,1)=3, "
                           "R_{1,2}(0,0)=2; brute force gives %s" % (sharp,))
    fails = 0
    tested_below = 0
    for (ell, aq) in sorted(BF):
        a, q = aq
        if ell + a + q + 1 > W:
            continue
        for s in range(0, max(0, a - 1)):
            checks += 1
            tested_below += 1
            if Rv(ell, a, q + 1, s + 1) != Rv(ell, a, q, s):
                fails += 1
    return dict(ok=True, checks=checks, seconds=time.time() - t0,
                detail="identity holds for every brute-force entry with "
                       "s >= a-1 and grade <= %d (%d of the right-hand sides are "
                       "nonzero); it fails for %d of the %d instances with "
                       "s < a-1, including the paper's R_{1,2}(1,1)=3 vs "
                       "R_{1,2}(0,0)=2" % (W, nontrivial[0], fails, tested_below))


def check_d2_complexity(nmax, verbose=False):
    """Corollary 7.4 (cor:d2-complexity).

    "The numbers |Av_n(12453)| for 0<=n<=N can be computed using O(N^7)
    exact-integer arithmetic operations and O(N^4) stored integers."

    The complexity statement is asymptotic and not finitely checkable.  What is
    checked: (a) the Section 7 reduced recurrence eq:R-recurrence together with
    the empty-stack recurrence eq:G, reduced by lem:d2-translation, reproduces
    |Av_n(12453)| for n <= 10 as computed by permuta; (b) the same holds when
    only the entries retained after lem:d2-second-translation are stored and
    the rest are recovered from eq:d2-second-translation; (c) the exact table
    sizes eq:d2-first-reduced-counts (binom(N+2,3) rows, N(N+1)(N^2+N+4)/12
    entries) and eq:d2-reduced-counts (N(N+1)(N^2+N+10)/24 retained entries)
    agree with the enumerated index sets for N <= 12.
    """
    t0 = time.time()
    NMAX = 10
    checks = 0
    got = reduced_counts(NMAX)
    got2 = reduced_counts_stored_only(NMAX)
    for n in range(NMAX + 1):
        want = avoider_count(n, C.beta(2))
        checks += 2
        if got[n] != want:
            return dict(ok=False, checks=checks, seconds=time.time() - t0,
                        detail="reduced recurrence gives %d at n=%d, permuta "
                               "gives %d" % (got[n], n, want))
        if got2[n] != want:
            return dict(ok=False, checks=checks, seconds=time.time() - t0,
                        detail="reduced recurrence with the lem:d2-second-"
                               "translation storage gives %d at n=%d, permuta "
                               "gives %d" % (got2[n], n, want))
    # (c) the exact table-size formulas
    for N in range(1, 13):
        rows = 0
        entries = 0
        retained = 0
        for ell in range(1, N + 1):
            for a in range(N - ell + 1):
                for q in range(N - ell - a + 1):
                    rows += 1
                    entries += (q + 1) if a == 0 else (a + q)
                    retained += 1 if a == 0 else a
        checks += 3
        if rows != _binom(N + 2, 3):
            return dict(ok=False, checks=checks, seconds=time.time() - t0,
                        detail="row count %d != binom(N+2,3)=%d at N=%d"
                               % (rows, _binom(N + 2, 3), N))
        if entries != N * (N + 1) * (N * N + N + 4) // 12:
            return dict(ok=False, checks=checks, seconds=time.time() - t0,
                        detail="entry count %d != eq:d2-first-reduced-counts %d "
                               "at N=%d" % (entries,
                                            N * (N + 1) * (N * N + N + 4) // 12, N))
        if retained != N * (N + 1) * (N * N + N + 10) // 24 or \
                retained != _binom(N + 1, 2) + _binom(N + 2, 4):
            return dict(ok=False, checks=checks, seconds=time.time() - t0,
                        detail="retained count %d != eq:d2-reduced-counts %d at "
                               "N=%d" % (retained,
                                         N * (N + 1) * (N * N + N + 10) // 24, N))
    return dict(ok=True, checks=checks, seconds=time.time() - t0,
                detail="reduced recurrence (and its lem:d2-second-translation "
                       "storage scheme) reproduce |Av_n(12453)| for n <= 10; the "
                       "row/entry-count formulas match the enumerated index sets "
                       "for N <= 12")


def _binom(n, k):
    if k < 0 or k > n:
        return 0
    r = 1
    for i in range(k):
        r = r * (n - i) // (i + 1)
    return r


def check_exact_150(nmax, verbose=False):
    """Proposition 8.1 (prop:exact-150) and the steps of its proof.

    "The file av12453_terms_0_150.txt contains the exact values |Av_n(12453)|
    for every 0 <= n <= 150."

    The multi-prime computation itself is not reproduced here.  Checked:
      (1) the file holds exactly the indices 0..150, its values for n <= 10
          agree with permuta's |Av_n(12453)| and its values for n <= 11 agree
          with eq:first-terms;
      (2) "Deleting the left-to-right minima of a 12453-avoider leaves a
          1342-avoider": verified by brute force for every element of
          Av_n(12453), n <= 8;
      (3) the resulting bound |Av_N(12453)| <= B_N of eq:exact-crt-bound,
          verified for N <= 10 against permuta, with b_m taken from the series
          expansion of Bona's generating function eq:bona-1342 (whose
          coefficients are also checked against permuta's |Av_m(1342)| for
          m <= 8), and the monotonicity of B_N used in the proof, for N <= 150;
      (4) "the product M of the eighteen largest [primes below 2^31] exceeds
          B_150; in fact M/B_150 > 1.92", with the primes recomputed here.
    """
    t0 = time.time()
    path = os.path.join(REPO, "code", "data", "av12453_terms_0_150.txt")
    terms = {}
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            n, v = line.split()
            terms[int(n)] = int(v)
    checks = 1
    if sorted(terms) != list(range(151)):
        return dict(ok=False, checks=checks, seconds=time.time() - t0,
                    detail="file does not contain exactly the indices 0..150")
    for n in range(11):
        checks += 1
        want = avoider_count(n, C.beta(2))
        if terms[n] != want:
            return dict(ok=False, checks=checks, seconds=time.time() - t0,
                        detail="file has %d at n=%d, permuta gives %d"
                               % (terms[n], n, want))
    first = [1, 1, 2, 6, 24, 119, 694, 4581, 33286, 260927, 2174398, 19053058]
    for n, v in enumerate(first):
        checks += 1
        if terms[n] != v:
            return dict(ok=False, checks=checks, seconds=time.time() - t0,
                        detail="file has %d at n=%d, eq:first-terms has %d"
                               % (terms[n], n, v))

    # (2) deleting the left-to-right minima leaves a 1342-avoider
    for n in range(9):
        for w in C.avoiders(n, C.beta(2)):
            checks += 1
            if not C.avoids(delete_lr_minima(w), (1, 3, 4, 2)):
                return dict(ok=False, checks=checks, seconds=time.time() - t0,
                            detail="%s avoids 12453 but deleting its "
                                   "left-to-right minima leaves %s, which "
                                   "contains 1342" % (w, delete_lr_minima(w)))

    # (3) eq:bona-1342 and the bound eq:exact-crt-bound
    b = bona_1342(150)
    for m in range(9):
        checks += 1
        if b[m] != avoider_count(m, (1, 3, 4, 2)):
            return dict(ok=False, checks=checks, seconds=time.time() - t0,
                        detail="eq:bona-1342 gives %d at m=%d, permuta gives %d"
                               % (b[m], m, avoider_count(m, (1, 3, 4, 2))))
    B = [crt_bound(N, b) for N in range(151)]
    for N in range(11):
        checks += 1
        if avoider_count(N, C.beta(2)) > B[N]:
            return dict(ok=False, checks=checks, seconds=time.time() - t0,
                        detail="|Av_%d(12453)| = %d exceeds B_%d = %d"
                               % (N, avoider_count(N, C.beta(2)), N, B[N]))
    for N in range(150):
        checks += 1
        if B[N] > B[N + 1]:
            return dict(ok=False, checks=checks, seconds=time.time() - t0,
                        detail="B_N is not nondecreasing at N=%d" % N)
    for n in range(151):
        checks += 1
        if terms[n] >= B[150]:
            return dict(ok=False, checks=checks, seconds=time.time() - t0,
                        detail="certified term %d at n=%d is not below B_150" % (
                            terms[n], n))

    # (4) the modulus
    primes = largest_primes_below(2 ** 31, 24)
    M = 1
    for q in primes[:18]:
        M *= q
    checks += 2
    if M <= B[150]:
        return dict(ok=False, checks=checks, seconds=time.time() - t0,
                    detail="the product of the eighteen largest primes below "
                           "2^31 does not exceed B_150")
    ratio = Fraction(M, B[150])
    if ratio <= Fraction(192, 100):
        return dict(ok=False, checks=checks, seconds=time.time() - t0,
                    detail="M/B_150 = %.6f, not > 1.92" % float(ratio))
    return dict(ok=True, checks=checks, seconds=time.time() - t0,
                detail="151 terms, agreeing with permuta for n <= 10 and with "
                       "eq:first-terms; LR-minima deletion maps Av_n(12453) into "
                       "Av(1342) for n <= 8; eq:bona-1342 reproduces |Av_m(1342)|; "
                       "|Av_N(12453)| <= B_N for N <= 10, B_N nondecreasing to "
                       "N=150, every certified term < B_150, and M/B_150 = %.4f "
                       "> 1.92 for the eighteen largest primes below 2^31"
                       % float(ratio))


def check_sampling(nmax, verbose=False):
    """Proposition 8.2 (prop:sampling) -- its uniformity content.

    "By the recursive method, such a path is uniformly random when every
    transition is chosen with probability proportional to the number of
    complete paths through it, that is, to the value of the corresponding
    summand of (eq:H). ... a given complete path from G_p is produced with
    probability 1/G_p; at p=(n,0,...,0) this is 1/|Av_n(beta_d)|."

    Compared: every complete path of eq:H from H_{(n,0)}(empty) is enumerated
    with exact Fraction probability = product over its transitions of
    (summand value)/(state value), the summands being the legal letters of
    prop:state-invariant(b) (the endpoint coefficient 2 appearing as the two
    letters of local rank 1 and ell_1).  Checked at each state visited: the
    recurrence value H_p(L) equals the number of complete paths below it, so
    the transition weights really are proportional to the number of complete
    paths through each transition (without this the product telescopes and
    says nothing).  Checked at the leaves: the letter sequence read off a path
    is compared with the elements of Av_n(12453) enumerated by permuta, and
    every probability with the exact rational 1/|Av_n(12453)|.  The O(n^4)
    operation count of the proposition is asymptotic and is not checked.
    """
    t0 = time.time()
    checks = 0
    nodes = 0
    for n in range(0, 9):
        dist, visited, mismatch = sampler_distribution(n, d=2)
        nodes += visited
        checks += visited
        if mismatch is not None:
            word, p, L, total, leaves = mismatch
            return dict(ok=False, checks=checks, seconds=time.time() - t0,
                        detail="after the prefix %s the state H_%s(%s) has value "
                               "%d but %d avoiding completions" % (
                                   word, p, L, total, leaves))
        want = set(C.avoiders(n, C.beta(2)))
        checks += 1
        if set(dist) != want:
            missing = sorted(want - set(dist))[:1]
            extra = sorted(set(dist) - want)[:1]
            return dict(ok=False, checks=checks, seconds=time.time() - t0,
                        detail="n=%d: paths are not in bijection with "
                               "Av_n(12453); missing %s, extra %s"
                               % (n, missing, extra))
        target = Fraction(1, len(want))
        for w, pr in dist.items():
            checks += 1
            if pr != target:
                return dict(ok=False, checks=checks, seconds=time.time() - t0,
                            detail="n=%d: path %s has probability %s, not %s"
                                   % (n, w, pr, target))
    return dict(ok=True, checks=checks, seconds=time.time() - t0,
                detail="for n <= 8 the complete paths of eq:H are exactly the "
                       "elements of Av_n(12453), each state value H_p(L) equals "
                       "the number of completions below it (%d states), and each "
                       "path has recursive-method probability exactly "
                       "1/|Av_n(12453)| (exact Fractions)" % nodes)


def check_wilf_class(nmax, verbose=False):
    """Section 10 (sec:discussion), the Wilf class of 12453.

    "The dihedral orbit of 12453 has eight elements, and the prefix-reversal
    equivalence of Backelin-West-Xin gives 12453 = 12 (+) 231 ~ 21 (+) 231 =
    21453, whose orbit supplies eight more.  Thus the algorithm, bounds, and
    certified coefficients apply to all sixteen members of the length-five Wilf
    class represented by 12453."

    Compared: the two dihedral orbits are computed from the definitions of
    reverse, complement and inverse (they must be disjoint and of size eight
    each), and |Av_n(tau)| is computed by brute force for every tau in S_5 and
    every n <= 8.  The sixteen must share the counting sequence of 12453, and
    every one of the remaining 104 patterns must differ from it at some n <= 8.
    """
    t0 = time.time()
    checks = 0
    orb1 = dihedral_orbit(C.beta(2))
    orb2 = dihedral_orbit((2, 1, 4, 5, 3))
    sixteen = orb1 | orb2
    checks += 3
    if len(orb1) != 8 or len(orb2) != 8 or len(sixteen) != 16:
        return dict(ok=False, checks=checks, seconds=time.time() - t0,
                    detail="orbit sizes are %d and %d, union %d (expected 8,8,16)"
                           % (len(orb1), len(orb2), len(sixteen)))
    counts = s5_avoider_counts(8)
    ref = counts[tuple(C.beta(2))]
    differ_at_8 = 0
    for p in sorted(counts):
        checks += 1
        same = counts[p] == ref
        if p not in sixteen and counts[p][8] != ref[8]:
            differ_at_8 += 1
        if p in sixteen and not same:
            return dict(ok=False, checks=checks, seconds=time.time() - t0,
                        detail="pattern %s is in the stated sixteen but has "
                               "counts %s != %s" % (p, counts[p], ref))
        if p not in sixteen and same:
            return dict(ok=False, checks=checks, seconds=time.time() - t0,
                        detail="pattern %s is outside the stated sixteen but "
                               "agrees with 12453 through n=8: %s" % (p, ref))
    return dict(ok=True, checks=checks, seconds=time.time() - t0,
                detail="the sixteen patterns share the sequence %s; each of the "
                       "other 104 length-five patterns differs from it at some "
                       "n <= 8, and %d of those 104 already differ at n = 8"
                       % (ref, differ_at_8))


def check_asymptotic_holdout(nmax, verbose=False):
    """Conjecture 10.1 (conj:12453-asymptotic) -- its finite, checkable content.

    The conjecture itself, an asymptotic expansion as n -> infinity with
    undetermined constants C, kappa, h, is not finitely checkable.  Section 10
    does, however, make one finite claim about the frozen fit:

      "The parameters kappa, log C, h were obtained by unweighted least squares
       on 70 <= n <= 100 ... the frozen values are
       (kappa, C, h) = (1.34550865, 0.82710184, 1.36800770) to the digits shown.
       On those fifty excluded coefficients, the maximum absolute difference
       between the observed and predicted values of log a_n is below
       4.3 * 10^{-7}."
      "The frozen fit gives e^{-kappa} approx 0.260."

    Compared: for every n in 101..150, log a_n with a_n read from the certified
    file code/data/av12453_terms_0_150.txt (whose first eleven entries are
    checked against permuta in prop:exact-150 above), against the model
    log a_n = n log mu - kappa n^{1/3} - (17/4) log n + log C + h n^{-1/3}
    with mu = 9 + 4 sqrt 2 and the three frozen constants as printed.  Nothing
    is refitted here: the constants come from the paper.
    """
    import math
    t0 = time.time()
    path = os.path.join(REPO, "code", "data", "av12453_terms_0_150.txt")
    terms = {}
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if line:
                n, v = line.split()
                terms[int(n)] = int(v)
    mu = 9.0 + 4.0 * math.sqrt(2.0)
    kappa, Cc, hh = 1.34550865, 0.82710184, 1.36800770
    checks = 0
    worst, argworst = 0.0, None
    for n in range(101, 151):
        checks += 1
        obs = math.log(terms[n])
        pred = (n * math.log(mu) - kappa * n ** (1.0 / 3.0)
                - (17.0 / 4.0) * math.log(n) + math.log(Cc)
                + hh * n ** (-1.0 / 3.0))
        if abs(obs - pred) > worst:
            worst, argworst = abs(obs - pred), n
    if worst >= 4.3e-7:
        return dict(ok=False, checks=checks, seconds=time.time() - t0,
                    detail="the frozen fit misses log a_%d by %.3e, the paper "
                           "claims a maximum below 4.3e-7" % (argworst, worst))
    checks += 1
    if abs(math.exp(-kappa) - 0.260) > 5e-4:
        return dict(ok=False, checks=checks, seconds=time.time() - t0,
                    detail="e^{-kappa} = %.5f, the paper says approx 0.260"
                           % math.exp(-kappa))
    return dict(ok=True, checks=checks, seconds=time.time() - t0,
                detail="the asymptotic expansion itself is not finitely "
                       "checkable; its frozen fit, held out on n = 101..150, "
                       "misses log a_n by at most %.3e (worst at n=%d), below "
                       "the paper's 4.3e-7, and e^{-kappa} = %.4f"
                       % (worst, argworst, math.exp(-kappa)))


def check_main_theorem(nmax, verbose=False):
    """Theorem 1.1 (thm:main).

    "For every fixed d>=1 and every N>=0, the numbers |Av_0(beta_d)|,...,
    |Av_N(beta_d)| can be computed using O_d(N^{3d+2}) exact-integer arithmetic
    operations and O_d(N^{2d+1}) stored integers.  All integers involved have
    O_d(N log N) bits."

    The complexity assertions are asymptotic and the theorem quantifies over
    all d, so it is not finitely checkable.  Finite instances checked: the
    algorithm of Section 6 (the kernel phase eq:K and the empty-stack phase
    eq:G, with eq:answer-G) is run for d = 1, 2, 3, 4 and its output compared
    with |Av_n(beta_d)| computed by permuta for every n <= 8; and the source
    region eq:source-region is enumerated for d <= 4, N <= 12 and its size
    compared with the count binom(N+d,d+1) of eq:row-count.
    """
    t0 = time.time()
    checks = 0
    for d in (1, 2, 3, 4):
        got = family_counts(d, nmax)
        for n in range(nmax + 1):
            want = avoider_count(n, C.beta(d))
            checks += 1
            if got[n] != want:
                return dict(ok=False, checks=checks, seconds=time.time() - t0,
                            detail="d=%d, n=%d: eq:K/eq:G algorithm gives %d, "
                                   "permuta gives %d" % (d, n, got[n], want))
    for d in (1, 2, 3, 4):
        for N in range(0, 13):
            rows = sum(1 for w in range(1, N + 1) for ell in range(1, w + 1)
                       for _ in controls(d, w - ell))
            checks += 1
            if rows != _binom(N + d, d + 1):
                return dict(ok=False, checks=checks, seconds=time.time() - t0,
                            detail="d=%d, N=%d: eq:source-region has %d rows, "
                                   "eq:row-count says %d"
                                   % (d, N, rows, _binom(N + d, d + 1)))
    return dict(ok=True, checks=checks, seconds=time.time() - t0,
                detail="the eq:K/eq:G algorithm reproduces |Av_n(beta_d)| for "
                       "d=1,2,3,4 and n <= %d (beta_1=1342, beta_2=12453, "
                       "beta_3=123564, beta_4=1234675); eq:row-count matches the "
                       "enumerated source region for d <= 4, N <= 12" % nmax)


# ======================================================================
# Driver
# ======================================================================

def run(nmax=8, verbose=False):
    results = []

    def add(statement, label, scope, res):
        row = dict(statement=statement, label=label, scope=scope,
                   checks=res["checks"], ok=res["ok"], detail=res["detail"],
                   seconds=round(res["seconds"], 3))
        results.append(row)
        if verbose:
            print("%-52s %-6s %6d checks  %5.2fs  %s"
                  % (statement, "OK" if row["ok"] else "FAIL", row["checks"],
                     row["seconds"], row["detail"]))

    add("Lemma 6.1 (kernel support)", "lem:support",
        "d = 1, 2, 3; all kernel sources (ell,p) with ell >= 1 and grade "
        "ell+||p||_1 <= 12 (d <= 2) or <= 10 (d = 3), each tested against every "
        "terminal control of mass <= the grade; the kernels are recomputed by "
        "stopped-path counting in the graph of eq:H, and by explicit "
        "enumeration of every path for grade <= 8",
        check_lem_support(nmax, verbose))

    add("Lemma 7.1 (exact two-threshold support)", "lem:d2-exact-support",
        "d = 2; brute-force stopped-path kernel rows for all 364 sources of "
        "grade <= 12, each compared with the stated support set over every "
        "terminal control (u,v) with u+v <= 12",
        check_d2_exact_support(nmax, verbose))

    add("Lemma 7.2 (first-coordinate translation)", "lem:d2-translation",
        "d = 2; every (ell,p,q,c,s) with grade ell+p+q <= 12, 0 <= c <= p, "
        "0 <= s <= 12, on the brute-force stopped-path kernel table; plus every "
        "entry of the eq:R-recurrence table of grade <= 12 against the "
        "brute-force value of K_ell((a,q),(0,s))",
        check_d2_translation(nmax, verbose))

    add("Lemma 7.3 (second-coordinate translation)", "lem:d2-second-translation",
        "d = 2; every brute-force reduced entry R_{ell,a}(q,s) with s >= a-1 "
        "and both grades <= 12, plus the paper's sharpness example and a census "
        "of the failures when s < a-1",
        check_d2_second_translation(nmax, verbose))

    add("Corollary 7.4 (sharpened 12453 bound)", "cor:d2-complexity",
        "the O(N^7)/O(N^4) bounds are asymptotic and not finitely checkable; "
        "finite content checked: the Section 7 reduced recurrence, with and "
        "without the lem:d2-second-translation storage scheme, reproduces "
        "|Av_n(12453)| for n <= 10 (permuta), and the exact table-size "
        "formulas hold for N <= 12",
        check_d2_complexity(nmax, verbose))

    add("Proposition 8.1 (computer-assisted certification)", "prop:exact-150",
        "the multi-prime computation is not reproduced here; finite content "
        "checked: the 151 entries of code/data/av12453_terms_0_150.txt against "
        "permuta for n <= 10 and eq:first-terms for n <= 11; the left-to-right "
        "minima deletion on all of Av_n(12453) for n <= 8; eq:bona-1342 against "
        "permuta for m <= 8; the bound B_N of eq:exact-crt-bound for N <= 10, "
        "its monotonicity to N = 150, and the size of the eighteen-prime "
        "modulus",
        check_exact_150(nmax, verbose))

    add("Proposition 8.2 (uniform random generation)", "prop:sampling",
        "d = 2; every complete path of eq:H from H_{(n,0)}(empty) and every "
        "state on it, for 0 <= n <= 8 (33286 paths at n=8), with exact "
        "Fraction probabilities.  This checks the uniformity argument on the "
        "literal recurrence eq:H; that the same distribution is obtained when "
        "the transition weights are read out of the stored R and G tables, and "
        "the O(n^4) operation count, are not checked here",
        check_sampling(nmax, verbose))

    add("Section 10 (Wilf class of 12453)", "sec:discussion",
        "all 120 patterns of S_5 and all permutations of length <= 8; "
        "Wilf-equivalence at EVERY length is not finitely checkable -- what is "
        "checked is that the stated sixteen agree through n = 8 and that no "
        "other length-five pattern does",
        check_wilf_class(nmax, verbose))

    add("Theorem 1.1 (main theorem)", "thm:main",
        "the complexity bounds are asymptotic and quantified over all d, hence "
        "not finitely checkable; finite instances checked: d = 1, 2, 3, 4 and "
        "n <= %d, the eq:K/eq:G algorithm against permuta, and the row count "
        "eq:row-count for d <= 4, N <= 12" % nmax,
        check_main_theorem(nmax, verbose))

    add("Conjecture 10.1 (asymptotics of |Av_n(12453)|)",
        "conj:12453-asymptotic",
        "the asymptotic expansion as n -> infinity, with constants C, kappa, h, "
        "is not finitely checkable; the finite claim attached to it is: with the "
        "constants frozen on 70 <= n <= 100, the model reproduces log a_n on the "
        "held-out range 101 <= n <= 150 to better than 4.3e-7, and "
        "e^{-kappa} = 0.260",
        check_asymptotic_holdout(nmax, verbose))

    return results


def main():
    t0 = time.time()
    rows = run(nmax=8, verbose=True)
    print()
    for r in rows:
        print("%-52s %-4s %8d checks %7.2fs" % (
            r["statement"], "OK" if r["ok"] else "FAIL", r["checks"], r["seconds"]))
    print("total %.1fs; all ok = %s" % (time.time() - t0, all(r["ok"] for r in rows)))


if __name__ == "__main__":
    main()
