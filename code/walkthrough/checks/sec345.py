"""Exhaustive checks of Sections 3, 4 and 5 of

    Protected tails and polynomial-time enumeration of permutations avoiding a
    direct sum of an increasing pattern and 231.

Every statement assigned to this module is checked by comparing an object
computed from the paper's displayed formulas with an object computed by brute
force from the definitions (permuta avoiders, explicit 231 tests, explicit
enumeration of paths in the recurrence graph).  Nothing here imports the
project's fast implementations; all formulas are retyped from the manuscript
and all brute-force routines are elementary.

Statements checked (paper numbering):

    Lemma 3.1      lem:least-trigger-frontier
    Prop. 4.1      prop:state-invariant (a), (b), (c)
    Theorem 4.3    thm:literal                    (eq:H, eq:initial-terminal)
    Cor. 4.4       cor:separators
    Prop. 4.5      prop:exponential
    Cor. 5.1       cor:protected-tail             (eq:factorization, eq:matrix-product)
    Prop. 5.2      prop:kernel-recurrence         (eq:K, eq:D)
    Cor. 5.3       cor:empty-stack-recurrence     (eq:G)

Run with PyPy:   pypy3 code/walkthrough/checks/sec345.py
"""
import os
import sys
import time
from functools import lru_cache
from itertools import combinations, permutations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from checks import common as C  # noqa: E402


# =====================================================================
#  Brute-force side: definitions only
# =====================================================================

def is_increasing(vals):
    return all(vals[i] < vals[i + 1] for i in range(len(vals) - 1))


def d_trigger_values(prefix, d):
    """The d-triggers of a word: entries that end an increasing d-subsequence.

    Definition of Section 2, by explicit enumeration of the subsequences.
    """
    out = []
    for pos in range(len(prefix)):
        for idx in combinations(range(pos), d - 1):
            if is_increasing([prefix[i] for i in idx] + [prefix[pos]]):
                out.append(prefix[pos])
                break
    return out


def is_trigger_after(prefix, x, d):
    """Is x a d-trigger of (prefix x)?  Explicit subsequence search."""
    if d == 1:
        return True
    for idx in combinations(range(len(prefix)), d - 1):
        vals = [prefix[i] for i in idx]
        if is_increasing(vals) and vals[-1] < x:
            return True
    return False


def thresholds(prefix, n, d):
    """The patience-sorting thresholds b_1 < ... < b_d of Section 3, by the
    definition: b_j is the smallest final entry of an increasing subsequence of
    length j inside the prefix, and the virtual value n + j when there is none.
    Computed by enumerating all increasing j-subsequences.
    """
    b = []
    for j in range(1, d + 1):
        best = None
        for idx in combinations(range(len(prefix)), j):
            vals = [prefix[i] for i in idx]
            if is_increasing(vals) and (best is None or vals[-1] < best):
                best = vals[-1]
        b.append(best if best is not None else n + j)
    return tuple(b)


def bands(prefix, n, d):
    """The unread blocks B_0 < ... < B_{d-1} of Section 3 (band 0 below b_1,
    band i between b_i and b_{i+1}), as tuples of values."""
    b = thresholds(prefix, n, d)
    unread = [v for v in range(1, n + 1) if v not in prefix]
    out = []
    for i in range(d):
        lo = 0 if i == 0 else b[i - 1]
        out.append(tuple(v for v in unread if lo < v < b[i]))
    return tuple(out), b


def scan_stack(prefix, n, d):
    """S(sigma) by Definition 2.4 (scan states and legal moves), transcribed:
    (a) merger, (b) split, (c) non-trigger move.  Returns the stack as a list
    of tuples, or None if the prefix is illegal."""
    stack = []
    read = ()
    for x in prefix:
        trig = d_trigger_values(read, d)
        q = min(trig) if trig else None
        x_is_trigger = is_trigger_after(read, x, d)
        if x_is_trigger and (q is None or x < q):                    # (a) merger
            E = tuple(v for v in range(1, n + 1)
                      if v not in read and v != x and v > x and (q is None or v < q))
            if stack:
                stack = [tuple(sorted(E + stack[0]))] + stack[1:]
            else:
                stack = [E] if E else []
        elif x_is_trigger and stack and x in stack[0]:                # (b) split
            lower = tuple(v for v in stack[0] if v < x)
            upper = tuple(v for v in stack[0] if v > x)
            stack = [I for I in (lower, upper) if I] + stack[1:]
        elif not x_is_trigger:                                        # (c) non-trigger
            pass
        else:
            return None                                               # illegal
        read = read + (x,)
    return stack


def scan_case(sigma, x, n, d):
    """Which case of Definition 2.4 applies when x is read from the legal prefix
    sigma: 'merger', 'split', 'non-trigger move', or 'illegal'."""
    stack = scan_stack(sigma, n, d)
    trig = d_trigger_values(sigma, d)
    q = min(trig) if trig else None
    if is_trigger_after(sigma, x, d):
        if q is None or x < q:
            return "merger"
        return "split" if (stack and x in stack[0]) else "illegal"
    return "non-trigger move"


def avoids231(w):
    """Explicit 231 test on a word with distinct entries."""
    for i, j, k in combinations(range(len(w)), 3):
        if w[k] < w[i] < w[j]:
            return False
    return True


def in_stack_language(w, stack):
    """Is w|_{I_1 u ... u I_s} in Av(231)(I_1) (+) ... (+) Av(231)(I_s)?"""
    union = set()
    for I in stack:
        union |= set(I)
    sub = [v for v in w if v in union]
    pos = 0
    for I in stack:
        block = sub[pos:pos + len(I)]
        if set(block) != set(I) or not avoids231(block):
            return False
        pos += len(I)
    return True


def satisfies_residual_obligations(prefix, w, d):
    """Does the completion w satisfy the residual obligations of every
    d-trigger of the prefix?  (Section 2: for a trigger c = sigma_j, the word
    (sigma_{j+1}...sigma_k w)|_{x > c} must avoid 231.)"""
    for j, c in enumerate(prefix):
        if not is_trigger_after(prefix[:j], c, d):
            continue
        tail = tuple(prefix[j + 1:]) + tuple(w)
        if not avoids231([v for v in tail if v > c]):
            return False
    return True


def corpus(n, d):
    """For every legal prefix of every beta_d-avoider of length n, the list of
    its beta_d-avoiding completions.  Built from permuta's Av only."""
    out = {}
    for pi in C.avoiders(n, C.beta(d)):
        for k in range(n + 1):
            out.setdefault(pi[:k], []).append(pi[k:])
    return out


_REALIZED = {}


def realized_states(n, d):
    """{(p, L): number of beta_d-avoiding completions} over every legal prefix of
    every beta_d-avoider of length <= n.  Pure brute force: the completions come
    from permuta's Av, the control from the thresholds, the stack from
    Definition 2.4."""
    if (n, d) in _REALIZED:
        return _REALIZED[(n, d)]
    out = {}
    for m in range(1, n + 1):
        for sigma, comps in corpus(m, d).items():
            stack = scan_stack(sigma, m, d)
            B, _b = bands(sigma, m, d)
            key = (tuple(len(Bi) for Bi in B), tuple(len(I) for I in stack))
            prev = out.setdefault(key, len(comps))
            assert prev == len(comps), "state %s realized with two different counts" % (key,)
    _REALIZED[(n, d)] = out
    return out


# =====================================================================
#  Paper side: the displayed formulas, retyped
# =====================================================================

def nz(L):
    return tuple(x for x in L if x)


def T(i, h, p):
    """eq:T:  T_{i,h}(p) = (p_0,...,p_{i-1}, h, p_{i+1}+p_i-1-h, p_{i+2},...)."""
    return p[:i] + (h, p[i + 1] + p[i] - 1 - h) + p[i + 2:]


def U(h, p):
    """eq:U:  U_h(p) = (p_0,...,p_{d-2}, h),  delta_h = p_{d-1}-1-h."""
    return p[:-1] + (h,)


@lru_cache(maxsize=None)
def H(p, L):
    """eq:H and eq:initial-terminal, transcribed literally."""
    if not any(p) and not L:
        return 1                                              # H_0(empty) = 1
    d = len(p)
    total = 0
    for i in range(d - 1):                                    # early-band moves
        for h in range(p[i]):
            total += H(T(i, h, p), L)
    for h in range(p[d - 1]):                                 # last band, merger
        delta = p[d - 1] - 1 - h
        head = (L[0] if L else 0) + delta
        total += H(U(h, p), nz((head,) + L[1:]))
    if L:
        l1 = L[0]
        total += min(2, l1) * H(p, nz((l1 - 1,) + L[1:]))     # endpoint choice
        for j in range(2, l1):                                # interior choice
            total += H(p, (j - 1, l1 - j) + L[1:])
    return total


def H_children(p, L):
    """The states on the right-hand side of eq:H, with multiplicity."""
    d = len(p)
    out = []
    for i in range(d - 1):
        for h in range(p[i]):
            out.append((T(i, h, p), L, 1))
    for h in range(p[d - 1]):
        delta = p[d - 1] - 1 - h
        head = (L[0] if L else 0) + delta
        out.append((U(h, p), nz((head,) + L[1:]), 1))
    if L:
        l1 = L[0]
        out.append((p, nz((l1 - 1,) + L[1:]), min(2, l1)))
        for j in range(2, l1):
            out.append((p, (j - 1, l1 - j) + L[1:], 1))
    return out


# ---- kernels by brute-force stopped-path enumeration in the graph of eq:H ----

def kernel_bruteforce(l, p, tail):
    """K_l^L(p, .) of Section 5 by definition: the number of paths in the graph
    of eq:H that start at H_p((l) | L), stop when L is first exposed, and stop
    at H_t(empty | L).  The path is tracked on the FULL composition M + L with
    a marker after M; the endpoint term counts as two labelled transitions when
    l_1 >= 2 (two distinct endpoints).  Asserts that the marked tail L is never
    touched before exposure.  Returns a dict t -> number of stopped paths."""
    memo = {}

    def go(p, M):
        if not M:
            return {p: 1}
        key = (p, M)
        if key in memo:
            return memo[key]
        acc = {}
        for (q, comp, mult) in H_children(p, M + tuple(tail)):
            m = len(comp) - len(tail)
            assert m >= 0 and tuple(comp[len(comp) - len(tail):]) == tuple(tail), \
                "a transition of eq:H changed the protected tail"
            for t, c in go(q, comp[:m]).items():
                acc[t] = acc.get(t, 0) + mult * c
        memo[key] = acc
        return acc

    return go(p, (l,))


@lru_cache(maxsize=None)
def K(l, p):
    """eq:K and eq:D, transcribed literally; returns a dict t -> K_l(p, t).
    Recursion is on the grade w = ||p||_1 + l, which every term lowers."""
    d = len(p)
    acc = {}

    def add(row, mult=1):
        for t, c in row.items():
            acc[t] = acc.get(t, 0) + mult * c

    for i in range(d - 1):
        for h in range(p[i]):
            add(K(l, T(i, h, p)))
    for h in range(p[d - 1]):
        delta = p[d - 1] - 1 - h
        add(K(l + delta, U(h, p)))
    if l == 1:                                        # eq:D
        add({p: 1})
    else:
        add(K(l - 1, p), 2)
    for a in range(1, l - 1):                         # a, b >= 1, a + b = l - 1
        b = l - 1 - a
        for u, c1 in K(a, p).items():
            for t, c2 in K(b, u).items():
                acc[t] = acc.get(t, 0) + c1 * c2
    return {t: c for t, c in acc.items() if c}


@lru_cache(maxsize=None)
def G(p):
    """eq:G with the boundary kernel K_0(p,t) = [p = t], transcribed."""
    d = len(p)
    total = 1 if not any(p) else 0
    for i in range(d - 1):
        for h in range(p[i]):
            total += G(T(i, h, p))
    for h in range(p[d - 1]):
        delta = p[d - 1] - 1 - h
        if delta == 0:
            total += G(U(h, p))                       # K_0 is the identity
        else:
            for t, c in K(delta, U(h, p)).items():
                total += c * G(t)
    return total


_ENUM = {}


def enumeration(d, n):
    """permuta's |Av_k(beta_d)| for k <= n."""
    if (d, n) not in _ENUM:
        from permuta import Av, Perm
        pat = C.beta(d)
        _ENUM[(d, n)] = Av([Perm(tuple(v - 1 for v in pat))]).enumeration(n)
    return _ENUM[(d, n)]


# =====================================================================
#  The checks
# =====================================================================

def check_lemma_31(nmax, dims, verbose=False):
    """Lemma 3.1 (least-trigger threshold).  'After a prefix has been read, let
    b_j be the smallest final entry of an increasing subsequence of length j
    contained in that prefix, for 1 <= j <= d; when the prefix contains no such
    subsequence, use the virtual value b_j = n + j.  Then b_1 < b_2 < ... < b_d.
    ...  Either b_d is virtual and no d-trigger has been read, or b_d is the
    smallest value of a d-trigger in the prefix.  Consequently, every unread
    value below b_d belongs to none of the projections onto larger values
    created by earlier triggers.  When b_d is nonvirtual, every unread value
    above b_d belongs to the projection created by the trigger b_d.'

    Also tested: the criterion used throughout Sections 3 and 4 (paragraph
    before the lemma, and after Definition 2.4) that an unread x is a
    d-trigger of (sigma x) exactly when x > b_{d-1}, with b_0 = 0.

    Compared: the thresholds computed from their definition by enumerating all
    increasing j-subsequences, against the d-triggers and the projections
    computed from their own definitions, for every prefix of every permutation
    of length <= nmax and every unread letter.
    """
    t0 = time.time()
    checks = 0
    for n in range(1, nmax + 1):
        prefixes = set()
        for pi in C.all_perms(n):
            for k in range(n + 1):
                prefixes.add(pi[:k])
        for sigma in prefixes:
            for d in dims:
                b = thresholds(sigma, n, d)
                unread = [v for v in range(1, n + 1) if v not in sigma]
                trig_d = d_trigger_values(sigma, d)
                # (1) the thresholds increase
                checks += 1
                if not is_increasing(b):
                    return False, "b_1 < ... < b_d fails at sigma=%s, d=%d: b=%s" % (sigma, d, b), checks, time.time() - t0
                # (2) b_d virtual iff no d-trigger; else b_d = least trigger
                checks += 1
                if trig_d:
                    if b[d - 1] != min(trig_d):
                        return False, "b_d != least d-trigger at sigma=%s, d=%d: b=%s trig=%s" % (sigma, d, b, trig_d), checks, time.time() - t0
                else:
                    if b[d - 1] != n + d:
                        return False, "b_d not virtual although no d-trigger, sigma=%s d=%d" % (sigma, d), checks, time.time() - t0
                # (3) unread values below b_d are in no projection of a trigger,
                #     unread values above a nonvirtual b_d are in the projection of b_d
                for x in unread:
                    checks += 1
                    in_some_projection = any(x > c for c in trig_d)
                    if x < b[d - 1]:
                        if in_some_projection:
                            return False, "unread %d < b_d lies in the projection of a trigger, sigma=%s d=%d" % (x, sigma, d), checks, time.time() - t0
                    elif trig_d and not x > b[d - 1]:
                        return False, "unread %d above b_d misordered, sigma=%s d=%d" % (x, sigma, d), checks, time.time() - t0
                # (4) the trigger criterion x is a d-trigger of (sigma x) iff x > b_{d-1}
                bprev = 0 if d == 1 else b[d - 2]
                for x in unread:
                    checks += 1
                    if is_trigger_after(sigma, x, d) != (x > bprev):
                        return False, "trigger criterion fails: sigma=%s d=%d x=%d b=%s" % (sigma, d, x, b), checks, time.time() - t0
    # the worked instance printed after the lemma: in 3 1 6 8 2 9 5 7 4 the
    # projection of the 2-trigger 6 onto larger values is 8, 9, 7 ~ 231, so
    # 3, 6, 8, 9, 7 is an occurrence of beta_2 = 12453, and the interspersed
    # values 2, 5, 4 below 6 are not in the projection.
    pi = (3, 1, 6, 8, 2, 9, 5, 7, 4)
    checks += 3
    if C.projection(pi, 2) != (8, 9, 7) or C.std((8, 9, 7)) != (2, 3, 1):
        return False, "the projection of 6 in 3 1 6 8 2 9 5 7 4 is not 8, 9, 7 ~ 231", checks, time.time() - t0
    if C.std((3, 6, 8, 9, 7)) != C.beta(2) or not C.contains(pi, C.beta(2)):
        return False, "3, 6, 8, 9, 7 is not an occurrence of beta_2 in 3 1 6 8 2 9 5 7 4", checks, time.time() - t0
    return True, ("thresholds vs. brute-force d-triggers and projections; "
                  "criterion 'x is a d-trigger of (sigma x) iff x > b_{d-1}' verified; "
                  "the worked instance 3 1 6 8 2 9 5 7 4 reproduced"), checks, time.time() - t0


def check_prop41a(nmax, d, verbose=False):
    """Proposition 4.1(a) (state invariant).  'The ordered layout
    B_0 < b_1 < B_1 < ... < b_d < I_1 < ... < I_s holds: the unread values below
    b_d form the d bands, and I_1 u ... u I_s is the set of unread values above
    b_d.  A completion w of sigma satisfies the residual obligations of all
    d-triggers of sigma exactly when w|_{I_1 u ... u I_s} lies in
    Av(231)(I_1) (+) ... (+) Av(231)(I_s); the base values are unrestricted by
    these obligations.'

    Compared: the stack of a legal prefix, computed from Definition 2.4, against
    the thresholds and bands computed from their definition (layout), and, for
    EVERY completion w of the prefix (all orderings of the unread letters, not
    only avoiding ones), the residual-obligation test made directly from the
    definition against membership in the stack language.
    """
    t0 = time.time()
    checks = 0
    for n in range(1, nmax + 1):
        legal = set()
        for pi in C.avoiders(n, C.beta(d)):
            for k in range(n + 1):
                legal.add(pi[:k])
        for sigma in sorted(legal):
            stack = scan_stack(sigma, n, d)
            if stack is None:
                return False, "prefix %s of an avoider is illegal" % (sigma,), checks, time.time() - t0
            B, b = bands(sigma, n, d)
            unread = [v for v in range(1, n + 1) if v not in sigma]
            # layout: bands are the unread values below b_d, stack is the rest
            checks += 1
            below = tuple(v for v in unread if v < b[d - 1])
            above = tuple(v for v in unread if v > b[d - 1])
            union = tuple(sorted(v for I in stack for v in I))
            if tuple(sorted(v for Bi in B for v in Bi)) != below or union != above:
                return False, "layout fails at sigma=%s: bands=%s stack=%s" % (sigma, B, stack), checks, time.time() - t0
            # the ordered layout itself
            for i in range(d):
                for v in B[i]:
                    checks += 1
                    lo = 0 if i == 0 else b[i - 1]
                    if not (lo < v < b[i]):
                        return False, "band %d misplaced at sigma=%s" % (i, sigma), checks, time.time() - t0
            # the obligation language, over every completion
            for w in permutations(unread):
                checks += 1
                if satisfies_residual_obligations(sigma, w, d) != in_stack_language(w, stack):
                    return False, ("obligation language fails: sigma=%s w=%s stack=%s"
                                   % (sigma, w, stack)), checks, time.time() - t0
    return True, ("layout and eq:obligation-language vs. the residual obligations "
                  "of every d-trigger, over every completion of every legal prefix"), checks, time.time() - t0


def check_prop41b(nmax, d, verbose=False):
    """Proposition 4.1(b) (state invariant).  'The legal moves from sigma, and
    their effect on (p, L), are the following.  A value of B_i with i < d-1
    having h unread values of B_i below it is a non-trigger move to
    (T_{i,h}(p), L).  A value of B_{d-1} having h unread values of B_{d-1} below
    it is a merger to (U_h(p), nz(l_1 + delta_h, l_2, ...)).  A value of I_1 of
    local rank r is a split to (p, nz(r-1, l_1-r, l_2, ...)).  No other letter is
    legal.'

    Also checked: the classification stated before Lemma 3.1, that in the terms
    of Definition 2.4 a value of B_i with i < d-1 is a non-trigger move, a value
    of B_{d-1} is a merger, and a value of I_1 is a split.

    Compared: for every legal prefix of every avoider and every unread letter x,
    the state (p', L') of the prefix sigma.x recomputed from the definitions
    (thresholds by subsequence search, stack by Definition 2.4) against the
    state predicted by eq:T / eq:U / the split rule; and legality (the existence
    of a legal move, Definition 2.4) against the brute-force criterion that
    sigma.x is a prefix of some beta_d-avoiding permutation.
    """
    t0 = time.time()
    checks = 0
    for n in range(1, nmax + 1):
        legal = set()
        for pi in C.avoiders(n, C.beta(d)):
            for k in range(n + 1):
                legal.add(pi[:k])
        for sigma in sorted(legal):
            stack = scan_stack(sigma, n, d)
            B, b = bands(sigma, n, d)
            p = tuple(len(Bi) for Bi in B)
            L = tuple(len(I) for I in stack)
            for x in range(1, n + 1):
                if x in sigma:
                    continue
                checks += 1
                new_stack = scan_stack(sigma + (x,), n, d)
                is_legal = new_stack is not None
                if is_legal != ((sigma + (x,)) in legal):
                    return False, ("legality disagrees with 'prefix of an avoider' at "
                                   "sigma=%s x=%d" % (sigma, x)), checks, time.time() - t0
                if not is_legal:
                    # the paper: every illegal letter lies in a deferred interval
                    if not any(x in I for I in stack[1:]):
                        return False, "illegal letter %d not in a deferred interval, sigma=%s" % (x, sigma), checks, time.time() - t0
                    continue
                # the classification stated before Lemma 3.1: a value of B_i with
                # i < d-1 is a non-trigger move, a value of B_{d-1} is a merger,
                # and a value of I_1 is a split
                where0 = [i for i in range(d) if x in B[i]]
                if where0:
                    want_case = "non-trigger move" if where0[0] < d - 1 else "merger"
                else:
                    want_case = "split"
                checks += 1
                if scan_case(sigma, x, n, d) != want_case:
                    return False, ("move classification fails: sigma=%s x=%d is a %s but the "
                                   "band position predicts %s" % (sigma, x, scan_case(sigma, x, n, d),
                                                                  want_case)), checks, time.time() - t0
                Bnew, bnew = bands(sigma + (x,), n, d)
                actual = (tuple(len(Bi) for Bi in Bnew), tuple(len(I) for I in new_stack))
                # predicted by Proposition 4.1(b)
                where = [i for i in range(d) if x in B[i]]
                if where:
                    i = where[0]
                    h = sum(1 for v in B[i] if v < x)
                    if i < d - 1:
                        pred = (T(i, h, p), L)
                    else:
                        delta = p[d - 1] - 1 - h
                        pred = (U(h, p), nz(((L[0] if L else 0) + delta,) + L[1:]))
                else:
                    r = sum(1 for v in stack[0] if v <= x)
                    pred = (p, nz((r - 1, L[0] - r) + L[1:]))
                if pred != actual:
                    return False, ("move prediction fails: sigma=%s x=%d predicted %s actual %s"
                                   % (sigma, x, pred, actual)), checks, time.time() - t0
    return True, ("eq:T / eq:U / split rule vs. the state of sigma.x recomputed from the "
                  "definitions; legality vs. 'sigma.x extends to an avoider'"), checks, time.time() - t0


def check_prop41c(nmax, d, verbose=False):
    """Proposition 4.1(c) (state invariant).  'Consequently, the set of
    beta_d-avoiding completions of sigma is determined, up to order isomorphism,
    by (p, L).'

    Compared: for every legal prefix of every avoider of length <= nmax, the SET
    of standardizations of its beta_d-avoiding completions (taken from permuta's
    avoiders) is grouped by the state (p, L) computed from the definitions; the
    check is that each group is a single set.
    """
    t0 = time.time()
    checks = 0
    for n in range(1, nmax + 1):
        seen = {}
        for sigma, comps in corpus(n, d).items():
            stack = scan_stack(sigma, n, d)
            B, b = bands(sigma, n, d)
            p = tuple(len(Bi) for Bi in B)
            L = tuple(len(I) for I in stack)
            key = (n - len(sigma), p, L)
            std = frozenset(C.std(w) for w in comps)
            checks += 1
            if key in seen:
                if seen[key][1] != std:
                    return False, ("two prefixes with state %s have different completion sets: "
                                   "%s and %s" % (key, seen[key][0], sigma)), checks, time.time() - t0
            else:
                seen[key] = (sigma, std)
    return True, "standardized sets of avoiding completions agree within every state (p, L)", checks, time.time() - t0


def check_thm43_states(nmax, d, verbose=False):
    """Theorem 4.3 (literal recurrence), state form.  'For every d >= 1,
    equations eq:H and eq:initial-terminal count every beta_d-avoiding
    permutation exactly once', where H_p(L) is defined (Section 4) as the number
    of completions of a legal prefix with state (p, L) that produce a
    beta_d-avoiding permutation.

    Compared: H_p(L) evaluated by the literal recurrence eq:H against the number
    of beta_d-avoiding completions of every legal prefix of every avoider of
    length <= nmax, the completions being taken from permuta's avoiders and the
    state (p, L) computed from the definitions.  Also checked, from the proof:
    eq:rho, rho(p,L) = ||p||_1 + sum l_j, drops by one on every transition of
    eq:H, and the only state without a successor is the zero state.
    """
    t0 = time.time()
    checks = 0
    for n in range(1, nmax + 1):
        for sigma, comps in corpus(n, d).items():
            stack = scan_stack(sigma, n, d)
            B, b = bands(sigma, n, d)
            p = tuple(len(Bi) for Bi in B)
            L = tuple(len(I) for I in stack)
            checks += 1
            if H(p, L) != len(comps):
                return False, ("H_%s(%s) = %d but prefix %s has %d avoiding completions"
                               % (p, L, H(p, L), sigma, len(comps))), checks, time.time() - t0
    # the termination argument of the proof, eq:rho: rho(p,L) = ||p||_1 + sum l_j
    # drops by one on every move, and the only terminal state is the zero state
    start = ((nmax,) + (0,) * (d - 1), ())
    seen, todo = set(), [start]
    while todo:
        st = todo.pop()
        if st in seen:
            continue
        seen.add(st)
        kids = H_children(*st)
        checks += 1
        if not kids and (any(st[0]) or st[1]):
            return False, "state %s has no successor but is not the zero state" % (st,), checks, time.time() - t0
        for (q, comp, _m) in kids:
            checks += 1
            if sum(q) + sum(comp) != sum(st[0]) + sum(st[1]) - 1:
                return False, "eq:rho does not drop by one from %s to %s" % (st, (q, comp)), checks, time.time() - t0
            if (q, comp) not in seen:
                todo.append((q, comp))
    return True, ("eq:H vs. the number of avoiding completions of every legal prefix; "
                  "eq:rho drops by one on each of the %d transitions reachable from "
                  "H_{(%d,0,...,0)}(empty)" % (sum(len(H_children(*st)) for st in seen), nmax)), checks, time.time() - t0


def check_thm43_counts(d, nmax, verbose=False):
    """Theorem 4.3 (literal recurrence), enumeration form: eq:initial-terminal,
    a_n^{(d)} = |Av_n(beta_d)| = H_{(n,0,...,0)}(empty).

    Compared: H_{(n,0,...,0)}(empty) from eq:H against permuta's enumeration of
    Av(beta_d).
    """
    t0 = time.time()
    checks = 0
    counts = enumeration(d, nmax)
    for n in range(nmax + 1):
        p = (n,) + (0,) * (d - 1)
        checks += 1
        if H(p, ()) != counts[n]:
            return False, ("H_%s(empty) = %d but |Av_%d(beta_%d)| = %d"
                           % (p, H(p, ()), n, d, counts[n])), checks, time.time() - t0
    return True, "H_{(n,0,...,0)}(empty) = %s = permuta's |Av_n(beta_%d)|" % (counts, d), checks, time.time() - t0


def move_label(sigma, x, n, d):
    """The label used in the tables of Examples 2.12 and 4.2 for reading x:
    'early band', 'last band' (+ ', merger' when the head grows), 'interior
    choice', 'endpoint choice', 'head exhausted'."""
    B, _b = bands(sigma, n, d)
    stack = scan_stack(sigma, n, d)
    for i in range(d):
        if x in B[i]:
            if i < d - 1:
                return "early band"
            h = sum(1 for v in B[i] if v < x)
            delta = len(B[i]) - 1 - h
            return "last band, merger" if delta > 0 else "last band"
    r = sum(1 for v in stack[0] if v <= x)
    if r == 1 or r == len(stack[0]):
        return "head exhausted" if len(stack[0]) == 1 else "endpoint choice"
    return "interior choice"


# The table of Example 4.2, transcribed: after each letter of the running
# example, the move, the thresholds b_1, b_2 (None for a virtual one), the
# bands B_0 and B_1, and the interval stack.
EX42_TABLE = [
    (9,  "early band",        (9, None), (1, 2, 3, 4, 5, 6, 7, 8), (10, 11, 12, 13, 14, 15), []),
    (11, "last band, merger", (9, 11),   (1, 2, 3, 4, 5, 6, 7, 8), (10,),  [(12, 13, 14, 15)]),
    (10, "last band",         (9, 10),   (1, 2, 3, 4, 5, 6, 7, 8), (),     [(12, 13, 14, 15)]),
    (14, "interior choice",   (9, 10),   (1, 2, 3, 4, 5, 6, 7, 8), (),     [(12, 13), (15,)]),
    (5,  "early band",        (5, 10),   (1, 2, 3, 4),             (6, 7, 8), [(12, 13), (15,)]),
    (12, "endpoint choice",   (5, 10),   (1, 2, 3, 4),             (6, 7, 8), [(13,), (15,)]),
    (6,  "last band, merger", (5, 6),    (1, 2, 3, 4),             (),     [(7, 8, 13), (15,)]),
    (2,  "early band",        (2, 6),    (1,),                     (3, 4), [(7, 8, 13), (15,)]),
    (3,  "last band, merger", (2, 3),    (1,),                     (),     [(4, 7, 8, 13), (15,)]),
    (8,  "interior choice",   (2, 3),    (1,),                     (),     [(4, 7), (13,), (15,)]),
    (4,  "endpoint choice",   (2, 3),    (1,),                     (),     [(7,), (13,), (15,)]),
    (7,  "head exhausted",    (2, 3),    (1,),                     (),     [(13,), (15,)]),
    (1,  "early band",        (1, 3),    (),                       (),     [(13,), (15,)]),
    (13, "head exhausted",    (1, 3),    (),                       (),     [(15,)]),
    (15, "head exhausted",    (1, 3),    (),                       (),     []),
]


def check_ex42(verbose=False):
    """Example 4.2 (what the second threshold adds).  The table of the d = 2
    scan of the running example pi = 9,11,10,14,5,12,6,2,3,8,4,7,1,13,15, the
    list of next choices from its eighth prefix, and the displayed expansion
    H_{(1,2)}((3,1)) = H_{(0,2)}((3,1)) + H_{(1,0)}((4,1)) + H_{(1,1)}((3,1))
    + 2 H_{(1,2)}((2,1)) + H_{(1,2)}((1,1,1)).

    Compared: every cell of the printed table (move, thresholds, bands, stack)
    against the same data recomputed from the definitions, the printed
    successors against the moves computed from the definitions, and the two
    sides of the displayed identity, the left by eq:H and the right by the
    successor states read off the definitions.
    """
    t0 = time.time()
    checks = 0
    pi = (9, 11, 10, 14, 5, 12, 6, 2, 3, 8, 4, 7, 1, 13, 15)
    n, d = 15, 2
    for k, (x, label, b_row, B0, B1, stack_row) in enumerate(EX42_TABLE):
        sigma = pi[:k]
        checks += 1
        if pi[k] != x:
            return False, "table row %d reads %d, the running example has %d" % (k + 1, x, pi[k]), checks, time.time() - t0
        if move_label(sigma, x, n, d) != label:
            return False, "row %d: move is '%s', table says '%s'" % (
                k + 1, move_label(sigma, x, n, d), label), checks, time.time() - t0
        B, b = bands(pi[:k + 1], n, d)
        stack = scan_stack(pi[:k + 1], n, d)
        checks += 3
        want_b = tuple(v if v is not None else n + j + 1 for j, v in enumerate(b_row))
        if b != want_b:
            return False, "row %d: thresholds %s, table says %s" % (k + 1, b, want_b), checks, time.time() - t0
        if (B[0], B[1]) != (B0, B1):
            return False, "row %d: bands %s, table says %s" % (k + 1, B, (B0, B1)), checks, time.time() - t0
        if [tuple(I) for I in stack] != stack_row:
            return False, "row %d: stack %s, table says %s" % (k + 1, stack, stack_row), checks, time.time() - t0
    # the successor table after the eighth letter, and the displayed identity
    sigma = pi[:8]
    B, b = bands(sigma, n, d)
    p = tuple(len(Bi) for Bi in B)
    stack = scan_stack(sigma, n, d)
    L = tuple(len(I) for I in stack)
    checks += 1
    if (p, L) != ((1, 2), (3, 1)):
        return False, "the eighth prefix has state H_%s(%s), the paper says H_(1,2)((3,1))" % (p, L), checks, time.time() - t0
    printed = {1: ((0, 2), (3, 1)), 3: ((1, 0), (4, 1)), 4: ((1, 1), (3, 1)),
               7: ((1, 2), (2, 1)), 13: ((1, 2), (2, 1)), 8: ((1, 2), (1, 1, 1))}
    for x, want in printed.items():
        checks += 1
        new_stack = scan_stack(sigma + (x,), n, d)
        Bn, _bn = bands(sigma + (x,), n, d)
        got = (tuple(len(Bi) for Bi in Bn), tuple(len(I) for I in new_stack))
        if got != want:
            return False, "successor of %d is H_%s(%s), the paper says H_%s(%s)" % (
                x, got[0], got[1], want[0], want[1]), checks, time.time() - t0
    checks += 1
    if scan_stack(sigma + (15,), n, d) is not None:
        return False, "reading 15 from the eighth prefix is legal, the paper says illegal", checks, time.time() - t0
    checks += 1
    rhs = (H((0, 2), (3, 1)) + H((1, 0), (4, 1)) + H((1, 1), (3, 1))
           + 2 * H((1, 2), (2, 1)) + H((1, 2), (1, 1, 1)))
    if H((1, 2), (3, 1)) != rhs:
        return False, "H_(1,2)((3,1)) = %d, the displayed expansion gives %d" % (
            H((1, 2), (3, 1)), rhs), checks, time.time() - t0
    return True, ("every cell of the printed table and every printed successor recomputed "
                  "from the definitions; H_(1,2)((3,1)) = %d both ways" % rhs), checks, time.time() - t0


def check_cor44(nmax, d, verbose=False):
    """Corollary 4.4 (separations of the stack).  'After a legal prefix has been
    read, let u < v be adjacent unread values above b_d.  The following are
    equivalent: (i) u and v lie in different intervals of the stack; (ii) some
    letter x with u < x < v was read after a d-trigger smaller than u; (iii) u
    precedes v in every beta_d-avoiding completion.  In particular, the stack is
    determined by the scanned prefix ...'  Also the remark after the proof: for
    arbitrary unread u < v above b_d, (i) and (iii) remain equivalent and hold
    exactly when some adjacent pair a < c with u <= a < c <= v satisfies (ii).

    Compared: (i) from the stack of Definition 2.4, (ii) read off the prefix
    directly, (iii) by scanning all beta_d-avoiding completions taken from
    permuta; and the stack rebuilt from the separations of (ii) against the
    stack of Definition 2.4.
    """
    t0 = time.time()
    checks = 0
    for n in range(1, nmax + 1):
        for sigma, comps in corpus(n, d).items():
            stack = scan_stack(sigma, n, d)
            B, b = bands(sigma, n, d)
            above = [v for v in range(1, n + 1) if v not in sigma and v > b[d - 1]]
            # (ii): positions of the d-triggers of the prefix
            trig_pos_val = [(j, sigma[j]) for j in range(len(sigma))
                            if is_trigger_after(sigma[:j], sigma[j], d)]

            def cond_ii(u, v):
                for j, x in enumerate(sigma):
                    if u < x < v and any(jj < j and cc < u for jj, cc in trig_pos_val):
                        return True
                return False

            def cond_i(u, v):
                iu = [k for k, I in enumerate(stack) if u in I][0]
                iv = [k for k, I in enumerate(stack) if v in I][0]
                return iu != iv

            def cond_iii(u, v):
                for w in comps:
                    if w.index(v) < w.index(u):
                        return False
                return True

            for a in range(len(above) - 1):
                u, v = above[a], above[a + 1]
                checks += 1
                i_, ii_, iii_ = cond_i(u, v), cond_ii(u, v), cond_iii(u, v)
                if not (i_ == ii_ == iii_):
                    return False, ("adjacent pair (%d,%d) of sigma=%s: (i)=%s (ii)=%s (iii)=%s"
                                   % (u, v, sigma, i_, ii_, iii_)), checks, time.time() - t0
            # the stack rebuilt from the separations of (ii)
            checks += 1
            rebuilt, cur = [], []
            for a, u in enumerate(above):
                cur.append(u)
                if a + 1 < len(above) and cond_ii(u, above[a + 1]):
                    rebuilt.append(tuple(cur))
                    cur = []
            if cur:
                rebuilt.append(tuple(cur))
            if rebuilt != [tuple(I) for I in stack]:
                return False, "stack rebuilt from (ii) is %s, definition gives %s at sigma=%s" % (
                    rebuilt, stack, sigma), checks, time.time() - t0
            # the remark: arbitrary pairs
            for a in range(len(above)):
                for c in range(a + 1, len(above)):
                    u, v = above[a], above[c]
                    checks += 1
                    i_ = cond_i(u, v)
                    iii_ = cond_iii(u, v)
                    some_adj = any(cond_ii(above[k], above[k + 1]) for k in range(a, c))
                    if not (i_ == iii_ == some_adj):
                        return False, ("arbitrary pair (%d,%d) of sigma=%s: (i)=%s (iii)=%s adj=%s"
                                       % (u, v, sigma, i_, iii_, some_adj)), checks, time.time() - t0
    return True, "(i) from the stack, (ii) from the prefix, (iii) from all avoiding completions", checks, time.time() - t0


def check_prop45(d, nmax, verbose=False):
    """Proposition 4.5.  'For fixed d >= 1 and n >= d+1, literal memoization of
    eq:H has at least F_{n-d} reachable composition keys when computing
    a_n^{(d)}, where F_{n-d} is the (n-d)th Fibonacci number.'  Its proof
    asserts that from H_{(n,0,...,0)}(empty) one reaches H_0((n-d)) and from
    there every positive composition L with |L| + len(L) = n - d + 1, of which
    there are sum_s binom(n-d-s, s-1) = F_{n-d}.

    Compared: the reachable states are enumerated explicitly by closing the
    right-hand side of eq:H under H_children from H_{(n,0,...,0)}(empty); the
    number of distinct compositions among them is compared with F_{n-d}, the
    claimed family of compositions is checked to be reachable, and the binomial
    sum of the proof is evaluated independently.
    """
    t0 = time.time()
    checks = 0
    for n in range(d + 1, nmax + 1):
        start = ((n,) + (0,) * (d - 1), ())
        seen, todo = set(), [start]
        while todo:
            st = todo.pop()
            if st in seen:
                continue
            seen.add(st)
            for (q, comp, _m) in H_children(*st):
                if (q, comp) not in seen:
                    todo.append((q, comp))
        keys = set(L for _p, L in seen)
        F = C.fibonacci(n - d)
        checks += 1
        if len(keys) < F:
            return False, "only %d composition keys reachable at n=%d, d=%d, F=%d" % (
                len(keys), n, d, F), checks, time.time() - t0
        # the proof's family
        target = set()
        def comps_with(total):
            # all positive compositions L with |L| + len(L) = total
            out = []
            def rec(cur, s):
                if s == total:
                    out.append(tuple(cur))
                    return
                for a in range(1, total - s):
                    if s + a + 1 <= total:
                        rec(cur + [a], s + a + 1)
            rec([], 0)
            return out
        for L in comps_with(n - d + 1):
            target.add(L)
            checks += 1
            if (tuple([0] * d), L) not in seen:
                return False, "composition %s of the proof is not reachable at the zero control (n=%d)" % (L, n), checks, time.time() - t0
        checks += 1
        if len(target) != F:
            return False, "the proof's family has %d members, F_{n-d} = %d (n=%d)" % (
                len(target), F, n), checks, time.time() - t0
        checks += 1
        binom_sum = sum(_binom(n - d - s, s - 1) for s in range(1, (n - d + 1) // 2 + 1))
        if binom_sum != F:
            return False, "sum of binomials = %d, F_{n-d} = %d (n=%d)" % (binom_sum, F, n), checks, time.time() - t0
    return True, ("reachable composition keys of eq:H counted explicitly and compared "
                  "with F_{n-d} and with the proof's family"), checks, time.time() - t0


def _binom(a, b):
    if b < 0 or a < 0 or b > a:
        return 0
    r = 1
    for i in range(b):
        r = r * (a - i) // (i + 1)
    return r


def check_cor51(d, wmax, tails, nreal=8, verbose=False):
    """Corollary 5.1 (permutation-stack factorization).  'The number
    K_l^L(p, t) is independent of L; denote it by K_l(p, t).  Then
    H_p((l)L) = sum_t K_l(p, t) H_t(L), and for L = (l_1,...,l_s),
    H_p(L) = sum_t (K_{l_1} K_{l_2} ... K_{l_s})(p, t) H_t(empty).'

    Compared: K_l^L(p, .) computed by explicit enumeration of stopped paths in
    the graph of eq:H (the tail L carried along and asserted untouched) for
    several different tails L; then eq:factorization and eq:matrix-product with
    those brute-force kernels against H computed by eq:H, for every source with
    grade ||p||_1 + l <= wmax.
    """
    t0 = time.time()
    checks = 0
    base = {}
    for w in range(1, wmax + 1):
        for p in _controls(d, w):
            l = w - sum(p)
            if l < 1:
                continue
            rows = [kernel_bruteforce(l, p, tail) for tail in tails]
            checks += len(rows) - 1
            for r in rows[1:]:
                if r != rows[0]:
                    return False, "K_%d(%s,.) depends on the tail: %s vs %s" % (
                        l, p, rows[0], r), checks, time.time() - t0
            base[(l, p)] = rows[0]
            # eq:factorization against eq:H, for several tails
            for tail in tails:
                checks += 1
                lhs = H(p, (l,) + tuple(tail))
                rhs = sum(c * H(t, tuple(tail)) for t, c in rows[0].items())
                if lhs != rhs:
                    return False, ("eq:factorization fails: H_%s(%s) = %d, sum_t K = %d"
                                   % (p, (l,) + tuple(tail), lhs, rhs)), checks, time.time() - t0
    # eq:matrix-product
    def matrix_product(p, L):
        vec = {p: 1}
        for li in L:
            nxt = {}
            for q, c in vec.items():
                kq = base.get((li, q))
                if kq is None:
                    kq = kernel_bruteforce(li, q, ())
                for t, c2 in kq.items():
                    nxt[t] = nxt.get(t, 0) + c * c2
            vec = nxt
        return vec

    for (l, p) in sorted(base):
        for tail in tails:
            L = (l,) + tuple(tail)
            if sum(p) + sum(L) > wmax:
                continue
            checks += 1
            if sum(c * H(t, ()) for t, c in matrix_product(p, L).items()) != H(p, L):
                return False, "eq:matrix-product fails at p=%s L=%s" % (p, L), checks, time.time() - t0
    # against brute force: every state realized by a legal prefix of an avoider
    real = realized_states(nreal, d)
    nreal_used = 0
    for (p, L), cnt in real.items():
        if not L:
            continue
        tail = L[1:]
        row = base.get((L[0], p))
        if row is None:
            row = kernel_bruteforce(L[0], p, tail)
        checks += 1
        nreal_used += 1
        rhs = sum(c * real.get((t, tail), H(t, tail)) for t, c in row.items())
        if cnt != rhs:
            return False, ("eq:factorization fails against brute force at (p,L) = (%s,%s): "
                           "%d avoiding completions, kernels give %d" % (p, L, cnt, rhs)), checks, time.time() - t0
        checks += 1
        rhs = sum(c * real.get((t, ()), H(t, ())) for t, c in matrix_product(p, L).items())
        if cnt != rhs:
            return False, ("eq:matrix-product fails against brute force at (p,L) = (%s,%s): "
                           "%d avoiding completions, kernel product gives %d" % (p, L, cnt, rhs)), checks, time.time() - t0
    return True, ("stopped-path kernels independent of L; eq:factorization and eq:matrix-product "
                  "reproduce eq:H and the brute-force completion counts of the %d nonempty-stack "
                  "states realized by avoiders of length <= %d" % (nreal_used, nreal)), checks, time.time() - t0


def _controls(d, w):
    """All controls p in N^d with ||p||_1 <= w."""
    out = []
    def rec(cur, rem):
        if len(cur) == d:
            out.append(tuple(cur))
            return
        for v in range(rem + 1):
            rec(cur + [v], rem - v)
    rec([], w)
    return out


def check_prop52(d, wmax, verbose=False):
    """Proposition 5.2 (compressed kernel recurrence), eq:K and eq:D.

    Compared: K_l(p, .) from the literal recurrence eq:K against K_l(p, .)
    computed by brute-force enumeration of stopped paths in the graph of eq:H,
    for every source of grade ||p||_1 + l <= wmax.  Also checked: the side
    condition a, b >= 1 in the split term and the coefficient 2 in eq:D are both
    load-bearing (mutating either makes the recurrence disagree).
    """
    t0 = time.time()
    checks = 0
    for w in range(1, wmax + 1):
        for p in _controls(d, w):
            l = w - sum(p)
            if l < 1:
                continue
            checks += 1
            brute = kernel_bruteforce(l, p, ())
            if K(l, p) != brute:
                return False, "K_%d(%s,.): eq:K gives %s, stopped paths give %s" % (
                    l, p, K(l, p), brute), checks, time.time() - t0
    # the side condition and the coefficient 2 must matter
    bad1 = _K_variant(d, wmax, allow_zero_parts=True)
    bad2 = _K_variant(d, wmax, endpoint_coeff=1)
    checks += 2
    detail = ("eq:K vs. brute-force stopped paths; dropping 'a,b >= 1' changes %d rows, "
              "using coefficient 1 instead of 2 changes %d rows" % (bad1, bad2))
    if bad1 == 0 or bad2 == 0:
        return False, "a mutation of eq:K left every kernel row unchanged: " + detail, checks, time.time() - t0
    return True, detail, checks, time.time() - t0


def _K_variant(d, wmax, allow_zero_parts=False, endpoint_coeff=2):
    """A deliberately mutated eq:K; returns the number of rows it gets wrong."""
    memo = {}

    def KV(l, p):
        if (l, p) in memo:
            return memo[(l, p)]
        acc = {}

        def add(row, mult=1):
            for t, c in row.items():
                acc[t] = acc.get(t, 0) + mult * c

        for i in range(len(p) - 1):
            for h in range(p[i]):
                add(KV(l, T(i, h, p)))
        for h in range(p[-1]):
            add(KV(l + p[-1] - 1 - h, U(h, p)))
        if l == 1:
            add({p: 1})
        else:
            add(KV(l - 1, p), endpoint_coeff)
        lo = 0 if allow_zero_parts else 1
        for a in range(lo, l - lo):
            b = l - 1 - a
            if b < lo:
                continue
            for u, c1 in KV(a, p).items() if a >= 1 else [(p, 1)]:
                for t, c2 in (KV(b, u).items() if b >= 1 else [(u, 1)]):
                    acc[t] = acc.get(t, 0) + c1 * c2
        memo[(l, p)] = {t: c for t, c in acc.items() if c}
        return memo[(l, p)]

    wrong = 0
    for w in range(1, wmax + 1):
        for p in _controls(d, w):
            l = w - sum(p)
            if l < 1:
                continue
            try:
                if KV(l, p) != kernel_bruteforce(l, p, ()):
                    wrong += 1
            except RecursionError:
                wrong += 1
    return wrong


def check_cor53(d, nmax, pmax, verbose=False):
    """Corollary 5.3 (empty-stack recurrence), eq:G, with eq:answer-G
    a_n^{(d)} = G_{(n,0,...,0)}.

    Compared: G_p from eq:G against H_p(empty) from eq:H (an identity between
    two formulas, computed by different routes: eq:G goes through the kernels
    K_{delta_h}, eq:H does not), against permuta's |Av_n(beta_d)| at
    p = (n,0,...,0), and against the brute-force number of avoiding completions
    of every legal prefix with an empty stack found in the avoiders of length
    <= nmax.
    """
    t0 = time.time()
    checks = 0
    counts = enumeration(d, nmax)
    for n in range(nmax + 1):
        p = (n,) + (0,) * (d - 1)
        checks += 1
        if G(p) != counts[n]:
            return False, "G_%s = %d but |Av_%d| = %d" % (p, G(p), n, counts[n]), checks, time.time() - t0
    for p in _controls(d, pmax):
        checks += 1
        if G(p) != H(p, ()):
            return False, "G_%s = %d but H_%s(empty) = %d" % (p, G(p), p, H(p, ())), checks, time.time() - t0
    # brute-force empty-stack states realized by legal prefixes of avoiders
    seen = 0
    for (p, L), cnt in realized_states(min(nmax, 8), d).items():
        if L:
            continue
        seen += 1
        checks += 1
        if G(p) != cnt:
            return False, "G_%s = %d but a legal prefix with that control has %d avoiding completions" % (
                p, G(p), cnt), checks, time.time() - t0
    return True, ("eq:G vs. eq:H, vs. permuta's counts at p=(n,0,...,0) for n <= %d, and vs. "
                  "the avoiding completions of the %d empty-stack controls realized by avoiders"
                  % (nmax, seen)), checks, time.time() - t0


# =====================================================================
#  Driver
# =====================================================================

def run(nmax=8, verbose=False):
    """Run every check of Sections 3-5 and return the list of result records."""
    results = []

    def record(statement, label, scope, res):
        ok, detail, checks, secs = res
        results.append(dict(statement=statement, label=label, scope=scope,
                            checks=checks, ok=ok, detail=detail, seconds=round(secs, 2)))
        if verbose:
            print("%-62s %s %8d checks %7.2fs  %s"
                  % (statement, "ok  " if ok else "FAIL", checks, secs, detail))

    n = min(nmax, 8)
    # lengths for the permuta enumerations of the initial condition
    n_enum = {2: min(10, n + 2), 3: min(9, n + 1)}

    record("Lemma 3.1 (least-trigger threshold)", "lem:least-trigger-frontier",
           "all %d prefixes of all permutations of length <= %d, every unread letter, d = 1, 2, 3"
           % (sum(_nprefixes(m) for m in range(1, n + 1)), n),
           check_lemma_31(n, (1, 2, 3), verbose))

    for d, pat in ((2, "12453"), (3, "123564")):
        record("Proposition 4.1(a) (state invariant: layout, language), d = %d" % d,
               "prop:state-invariant",
               "every legal prefix of every %s-avoider of length <= %d, and every one of its "
               "completions (all orderings of the unread letters, not only avoiding ones)"
               % (pat, n),
               check_prop41a(n, d, verbose))
        record("Proposition 4.1(b) (state invariant: legal moves), d = %d" % d,
               "prop:state-invariant",
               "every legal prefix of every %s-avoider of length <= %d and every unread letter"
               % (pat, n),
               check_prop41b(n, d, verbose))
        record("Proposition 4.1(c) (state invariant: (p,L) determines the completions), d = %d" % d,
               "prop:state-invariant",
               "every legal prefix of every %s-avoider of length <= %d, grouped by (p, L)"
               % (pat, n),
               check_prop41c(n, d, verbose))
        record("Theorem 4.3 (literal recurrence eq:H at every state), d = %d" % d, "thm:literal",
               "every legal prefix of every %s-avoider of length <= %d" % (pat, n),
               check_thm43_states(n, d, verbose))
        record("Theorem 4.3 (initial condition, eq:initial-terminal), d = %d" % d, "thm:literal",
               "H_{(k,0,...,0)}(empty) vs. permuta's |Av_k(%s)| for k <= %d" % (pat, n_enum[d]),
               check_thm43_counts(d, n_enum[d], verbose))
        if d == 2:
            record("Example 4.2 (what the second threshold adds)", "ex:full-state",
                   "the printed table and successor list of the running example "
                   "pi = 9,11,10,14,5,12,6,2,3,8,4,7,1,13,15, d = 2, pattern 12453",
                   check_ex42(verbose))
        record("Corollary 4.4 (separations of the stack), d = %d" % d, "cor:separators",
               "every adjacent and every non-adjacent unread pair above b_d, for every legal "
               "prefix of every %s-avoider of length <= %d" % (pat, n),
               check_cor44(n, d, verbose))
        record("Proposition 4.5 (exponential literal state space), d = %d" % d, "prop:exponential",
               "all states reachable from H_{(k,0,...,0)}(empty) under eq:H, d < k <= %d "
               "(the asymptotic statement itself is not finitely checkable; the finite instance "
               "'at least F_{k-d} reachable composition keys' is)" % (14 - d),
               check_prop45(d, 14 - d, verbose))
        record("Corollary 5.1 (permutation-stack factorization), d = %d" % d, "cor:protected-tail",
               "every kernel source (p, l) of grade ||p||_1 + l <= 8, five protected tails L, "
               "and every state realized by a legal prefix of a %s-avoider of length <= %d"
               % (pat, n),
               check_cor51(d, 8, [(), (1,), (3,), (2, 1), (1, 2, 1)], n, verbose))
        record("Proposition 5.2 (compressed kernel recurrence), d = %d" % d,
               "prop:kernel-recurrence",
               "every kernel source (p, l) of grade ||p||_1 + l <= %d" % (14 - d),
               check_prop52(d, 14 - d, verbose))
        record("Corollary 5.3 (empty-stack recurrence), d = %d" % d, "cor:empty-stack-recurrence",
               "every control of mass <= 8, p = (k,0,...,0) for k <= %d, and every empty-stack "
               "state realized by a legal prefix of a %s-avoider of length <= %d"
               % (n_enum[d], pat, n),
               check_cor53(d, n_enum[d], 8, verbose))

    return results


def _nprefixes(m):
    total, f = 0, 1
    for k in range(m + 1):
        total += f
        f = f * (m - k) if k < m else f
    return total


if __name__ == "__main__":
    t0 = time.time()
    out = run(nmax=int(sys.argv[1]) if len(sys.argv) > 1 else 8, verbose=True)
    print()
    for r in out:
        print("%-4s %-58s %s" % ("OK" if r["ok"] else "FAIL", r["statement"], r["detail"]))
    print("\ntotal %.1fs, %d checks, %d/%d statements ok"
          % (time.time() - t0, sum(r["checks"] for r in out),
             sum(1 for r in out if r["ok"]), len(out)))
