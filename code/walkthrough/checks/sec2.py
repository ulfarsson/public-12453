"""Exhaustive checks of the statements of Section 2 of

    Protected tails and polynomial-time enumeration of permutations
    avoiding a direct sum of an increasing pattern and 231,

the one-threshold prototype (d = 1) together with the general-d statements
that Section 2 proves for every d.

Every check compares an object built from the paper's displayed formulas or
constructions with an object built by brute force from the definitions
(permuta for pattern containment, explicit enumeration of completions,
explicit enumeration of paths in the recurrence graph).  Nothing in this
file is imported from the paper's reference implementations in `code/`.

Run with PyPy:  pypy3 code/walkthrough/checks/sec2.py
"""
import os
import sys
import time
from collections import defaultdict
from functools import lru_cache
from itertools import permutations, product

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from checks import common as C  # noqa: E402


# ===================================================================== basics
# Brute-force transcriptions of the definitions of Section 2.

def avoids_231(w):
    """True if the word w (distinct entries) avoids 231."""
    n = len(w)
    for k in range(2, n):
        c = w[k]
        for i in range(k):
            if w[i] > c:
                for j in range(i + 1, k):
                    if w[j] > w[i]:
                        return False
    return True


def triggers(w, d):
    """The values of the d-triggers of w: entries ending an increasing
    d-subsequence (Section 2, first paragraph)."""
    lis = C.lis_ending(w)
    return frozenset(v for v, l in zip(w, lis) if l >= d)


def is_trigger_of(prefix, x, d):
    """True if x is a d-trigger of (prefix, x)."""
    return C.lis_ending(tuple(prefix) + (x,))[-1] >= d


def unread_letters(prefix, n):
    s = set(prefix)
    return tuple(v for v in range(1, n + 1) if v not in s)


def legal_move(prefix, stack, x, n, d):
    """Definition 2.4, transcribed.  Returns (kind, new stack) for a legal
    move reading the unread letter x from the scan state (prefix, stack), and
    None when reading x is illegal."""
    trig = triggers(prefix, d)
    q = min(trig) if trig else None
    unread = [v for v in unread_letters(prefix, n) if v != x]
    x_trig = is_trigger_of(prefix, x, d)
    if x_trig and (q is None or x < q):                      # (a) merger
        E = tuple(v for v in unread if v > x and (q is None or v < q))
        if stack:
            new = (tuple(sorted(E + stack[0])),) + stack[1:]
        else:
            new = (E,) if E else ()
        return "merger", new
    if x_trig and stack and x in stack[0]:                   # (b) split
        lo = tuple(v for v in stack[0] if v < x)
        hi = tuple(v for v in stack[0] if v > x)
        kind = "interior" if lo and hi else "endpoint"
        return "split/" + kind, tuple(I for I in (lo, hi) if I) + stack[1:]
    if not x_trig:                                           # (c) non-trigger
        return "non-trigger", stack
    return None                                              # illegal


def is_scan_state(prefix, stack, n, d):
    """Definition 2.4: a list of nonempty sets I_1 < ... < I_s whose union is
    the set of unread letters larger than the least d-trigger of the prefix
    (empty when the prefix has no d-trigger)."""
    trig = triggers(prefix, d)
    unread = set(unread_letters(prefix, n))
    want = {v for v in unread if v > min(trig)} if trig else set()
    if any(len(I) == 0 for I in stack):
        return False
    if any(max(I) >= min(J) for I, J in zip(stack, stack[1:])):
        return False
    return {v for I in stack for v in I} == want


def legal_states(n, d):
    """All legal words of [n] with their stacks, generated from the initial
    state by legal moves only (Definition 2.4)."""
    out = []

    def rec(prefix, stack):
        out.append((prefix, stack))
        for x in unread_letters(prefix, n):
            move = legal_move(prefix, stack, x, n, d)
            if move is not None:
                rec(prefix + (x,), move[1])

    rec((), ())
    return out


# ----------------------------------------------- residual obligations, stacks

def creates_231(w, y):
    """True if appending y to the 231-avoiding word w creates a 231, i.e. if
    w has an increasing pair above y."""
    best = None
    for v in w:
        if v > y:
            if best is not None and v > best:
                return True
            if best is None or v < best:
                best = v
    return False


def allowed_orders(prefix, n, d):
    """Brute force.  All orders w of the unread letters above the least
    d-trigger q of the prefix such that every residual obligation of every
    d-trigger c of the prefix holds, i.e. (sigma_{j+1}..sigma_k w)|_{x>c}
    avoids 231.  (Letters below q occur in no such projection.)  Built by
    depth-first search with the monotone pruning `no obligation is violated
    by the part read so far'."""
    prefix = tuple(prefix)
    trig = sorted(triggers(prefix, d))
    if not trig:
        return {()}
    q = trig[0]
    vals = tuple(v for v in unread_letters(prefix, n) if v > q)
    fixed = {c: tuple(v for v in prefix[j + 1:] if v > c)
             for j, c in enumerate(prefix) if c in trig}
    out = set()

    def rec(cur, rest):
        if not rest:
            out.add(cur)
            return
        for i, y in enumerate(rest):
            ok = True
            for c in trig:
                if y > c and creates_231(fixed[c] + tuple(v for v in cur if v > c), y):
                    ok = False
                    break
            if ok:
                rec(cur + (y,), rest[:i] + rest[i + 1:])

    rec((), vals)
    return out


@lru_cache(maxsize=None)
def av231_patterns(k):
    return tuple(p for p in permutations(range(k)) if avoids_231(p))


def language(stack):
    """Av(231)(I_1) (+) ... (+) Av(231)(I_s) as a set of words."""
    blocks = []
    for I in stack:
        vals = sorted(I)
        blocks.append([tuple(vals[i] for i in pat) for pat in av231_patterns(len(vals))])
    return {tuple(v for blk in combo for v in blk) for combo in product(*blocks)}


def stack_from_orders(vals, orders):
    """The stack determined by a set of allowed orders: consecutive values are
    cut apart exactly when the smaller one precedes the larger one in every
    allowed order.  Returns None if no stack has this language."""
    vals = sorted(vals)
    stack, cur = [], [vals[0]] if vals else []
    for u, v in zip(vals, vals[1:]):
        always = all(w.index(u) < w.index(v) for w in orders)
        if always:
            stack.append(tuple(cur))
            cur = [v]
        else:
            cur.append(v)
    if cur:
        stack.append(tuple(cur))
    stack = tuple(stack)
    return stack if language(stack) == set(orders) else None


# ================================================= the paper's scalar formulas

def nz(*xs):
    return tuple(x for x in xs if x != 0)


@lru_cache(maxsize=None)
def W(p, L):
    """W_p(L) from (eq:W), (eq:W-endpoint) and (eq:W-boundary)."""
    if not L:                                                    # (eq:W-boundary)
        return (1 if p == 0 else 0) + sum(W(h, nz(p - 1 - h)) for h in range(p))
    ell, Lp = L[0], L[1:]
    total = sum(W(h, (ell + p - 1 - h,) + Lp) for h in range(p))  # base moves
    total += W(p, Lp) if ell == 1 else 2 * W(p, (ell - 1,) + Lp)  # (eq:W-endpoint)
    for a in range(1, ell - 1):                                   # interior choices
        total += W(p, (a, ell - 1 - a) + Lp)
    return total


@lru_cache(maxsize=None)
def Krow(ell, p):
    """K_ell(p, .) from (eq:scalar-K) and (eq:scalar-D), as a dict t -> value."""
    if ell == 0:
        return {p: 1}
    res = defaultdict(int)
    for h in range(p):
        for t, v in Krow(ell + p - 1 - h, h).items():
            res[t] += v
    if ell == 1:
        res[p] += 1
    else:
        for t, v in Krow(ell - 1, p).items():
            res[t] += 2 * v
    for a in range(1, ell - 1):
        b = ell - 1 - a
        for u, va in Krow(a, p).items():
            for t, vb in Krow(b, u).items():
                res[t] += va * vb
    return {t: v for t, v in res.items() if v}


@lru_cache(maxsize=None)
def G(p):
    """G_p from (eq:scalar-G)."""
    total = 1 if p == 0 else 0
    for h in range(p):
        for t, v in Krow(p - 1 - h, h).items():
            total += v * G(t)
    return total


def kernel_by_paths(ell, p, L):
    """K_ell(p, .) by brute force: enumerate the paths of the recurrence graph
    of (eq:W) that start at (p, (ell)|L) and are stopped at the first exposure
    of L, and record the control there.  Every summand of (eq:W) is one
    transition; the coefficient-2 endpoint term of (eq:W-endpoint) is two
    transitions."""
    counts = defaultdict(int)

    def walk(p_cur, S):
        if S == L:                                # first exposure of the tail
            counts[p_cur] += 1
            return
        ell0, rest = S[0], S[1:]
        for h in range(p_cur):
            walk(h, (ell0 + p_cur - 1 - h,) + rest)
        if ell0 == 1:
            walk(p_cur, rest)
        else:
            walk(p_cur, (ell0 - 1,) + rest)
            walk(p_cur, (ell0 - 1,) + rest)
        for a in range(1, ell0 - 1):
            walk(p_cur, (a, ell0 - 1 - a) + rest)

    walk(p, (ell,) + L)
    return dict(counts)


def catalan(k):
    num, den = 1, 1
    for i in range(k):
        num *= 2 * k - i
        den *= i + 1
    return num // den // (k + 1)


def compositions_upto(total):
    """All compositions L (tuples of positive parts) with |L| <= total."""
    out = [()]
    frontier = [()]
    while frontier:
        nxt = []
        for L in frontier:
            room = total - sum(L)
            for a in range(1, room + 1):
                nxt.append(L + (a,))
        out.extend(nxt)
        frontier = nxt
    return out


# ======================================================= brute-force reference

_STATES = {}


def states_cached(n, d):
    if (n, d) not in _STATES:
        _STATES[(n, d)] = legal_states(n, d)
    return _STATES[(n, d)]


_AVOIDERS = {}


def avoiders_cached(n, d):
    if (n, d) not in _AVOIDERS:
        _AVOIDERS[(n, d)] = C.avoiders(n, C.beta(d))
    return _AVOIDERS[(n, d)]


def prefix_counts(n, d):
    """prefix -> number of beta_d-avoiders of length n with that prefix."""
    out = defaultdict(int)
    for pi in avoiders_cached(n, d):
        for k in range(n + 1):
            out[pi[:k]] += 1
    return out


def dlist(ds):
    return "d = " + ", ".join(str(d) for d in ds)


def result(statement, label, scope, checks, ok, detail, seconds):
    return dict(statement=statement, label=label, scope=scope, checks=checks,
                ok=ok, detail=detail, seconds=seconds)


# ============================================================ Lemma 2.1

def check_trigger(nmax):
    """Lemma 2.1 (trigger lemma).  `A permutation pi avoids beta_d if and only
    if, for every increasing d-subsequence ending at c = pi_j, the word
    pi_{j+1}...pi_n|_{x > pi_j} avoids 231 after standardization.'

    Compared: membership of pi in Av_n(beta_d) as computed by permuta, versus
    the right-hand side evaluated directly -- for every d-trigger position j
    (the positions ending an increasing d-subsequence, from lis_ending), the
    projection of the suffix onto the values above pi_j avoids 231.
    """
    t0 = time.time()
    checks, bad = 0, None
    for d in (1, 2, 3):
        for n in range(1, nmax + 1):
            av = set(avoiders_cached(n, d))
            for pi in C.all_perms(n):
                lhs = pi in av
                rhs = all(avoids_231(C.projection(pi, j))
                          for j in C.trigger_positions(pi, d))
                checks += 1
                if lhs != rhs and bad is None:
                    bad = "d=%d pi=%s: permuta avoids=%s, trigger condition=%s" % (
                        d, pi, lhs, rhs)
    return result(
        "Lemma 2.1 (trigger lemma)", "lem:trigger",
        "all permutations of length <= %d, d = 1, 2, 3 (patterns 1342, 12453, 123564)" % nmax,
        checks, bad is None,
        bad or "avoidance of beta_d (permuta) agrees with 231-avoidance of every "
               "d-trigger projection for every permutation tested",
        time.time() - t0)


# ============================================================ Lemma 2.2

def check_first_letter(nmax):
    """Lemma 2.2 (first-letter lemma).  `A permutation of I beginning with x
    avoids 231 if and only if all values below x occur before all values above
    x, and the two induced subwords avoid 231.  Thus reading x replaces an
    interval of size l by intervals of sizes r-1, l-r.'

    Compared, in both directions, for I = [n] and every permutation w of [n]
    (so every first letter x and every local rank r = x): brute-force
    231-avoidance of w, versus the conjunction of the three conditions of the
    lemma, evaluated directly on w.  Also compared: the sizes of the two
    induced subwords versus r-1 and l-r.
    """
    t0 = time.time()
    checks, bad = 0, None
    for n in range(1, nmax + 1):
        for w in C.all_perms(n):
            x = w[0]
            r = x                       # local rank of x in I = [n]
            below = tuple(v for v in w[1:] if v < x)
            above = tuple(v for v in w[1:] if v > x)
            split_ok = all(w[1:].index(u) < w[1:].index(a)
                           for u in below for a in above)
            rhs = split_ok and avoids_231(below) and avoids_231(above)
            lhs = avoids_231(w)
            checks += 2
            if bad is None and lhs != rhs:
                bad = "w=%s: avoids 231 = %s, lemma condition = %s" % (w, lhs, rhs)
            if bad is None and (len(below), len(above)) != (r - 1, n - r):
                bad = "w=%s: subword sizes %s, lemma says %s" % (
                    w, (len(below), len(above)), (r - 1, n - r))
    return result(
        "Lemma 2.2 (first-letter lemma)", "lem:first-letter",
        "I = [n] and all n! permutations of I, n <= %d (every first letter and "
        "every local rank); both directions of the iff, and the two part sizes" % nmax,
        checks, bad is None,
        bad or "231-avoidance agrees with the split condition, and the induced "
               "subwords have sizes r-1 and l-r, for every permutation tested",
        time.time() - t0)


# ================================================= Definition 2.4 / Lemma 2.5

def check_legal_moves(nmax, ds=(1, 2, 3)):
    """Definition 2.4 and Lemma 2.5 (legal moves).  `(a) If reading x is a
    legal move, then (sigma x, S') is a scan state.  (b) Reading x is illegal
    if and only if x lies in a deferred interval I_2, ..., I_s.'

    The legal words and their stacks are generated from the initial state by
    the three moves of Definition 2.4 alone.  For every such scan state and
    every unread letter x: (a) when the move is legal, the resulting pair is
    tested against the definition of a scan state (nonempty sets, strictly
    increasing, union equal to the set of unread letters above the least
    d-trigger of sigma x), computed from sigma x directly; (b) `no legal move
    of Definition 2.4 applies' is compared with `x lies in one of
    I_2, ..., I_s'.
    """
    t0 = time.time()
    checks, bad = 0, None
    for d in ds:
        for n in range(1, nmax + 1):
            for prefix, stack in states_cached(n, d):
                deferred = {v for I in stack[1:] for v in I}
                for x in unread_letters(prefix, n):
                    move = legal_move(prefix, stack, x, n, d)
                    checks += 1
                    if bad is None and (move is None) != (x in deferred):
                        bad = "d=%d n=%d sigma=%s stack=%s x=%d: illegal=%s, in deferred=%s" % (
                            d, n, prefix, stack, x, move is None, x in deferred)
                    if move is not None:
                        checks += 1
                        if bad is None and not is_scan_state(prefix + (x,), move[1], n, d):
                            bad = "d=%d n=%d sigma=%s x=%d: %s is not a scan state" % (
                                d, n, prefix, x, (move[1],))
    return result(
        "Definition 2.4 / Lemma 2.5 (legal moves)", "lem:legal-moves",
        "%s; every legal word of [n] with its stack (generated by the "
        "moves of Definition 2.4 from the initial state) for n <= %d, and every "
        "unread letter" % (dlist(ds), nmax),
        checks, bad is None,
        bad or "every legal move lands in a scan state, and illegality coincides "
               "exactly with membership in a deferred interval",
        time.time() - t0)


# ================================================= Definition 2.6 / Lemma 2.8

def check_merger(nmax, ds=(1, 2, 3)):
    """Definition 2.6 and Lemma 2.8 (stack merger).  `(a) If sigma has no
    d-trigger then S is empty and (E), E the unread letters above x, is
    faithful to sigma x.  (b) Otherwise E is empty or an interval of the unread
    alphabet; if s >= 1 then E < I_1 and E u I_1 is an interval of the unread
    alphabet; and (E u I_1, I_2, ..., I_s) is faithful to sigma x, only the
    active head changing.'

    Compared: the stack the lemma predicts, versus the faithful stack of
    sigma x computed from Definition 2.6 by brute force -- the set A of orders
    of the unread letters above x satisfying the residual obligations of every
    d-trigger of sigma x is enumerated directly from the definition of a
    residual obligation, the unique stack whose language is A is reconstructed
    from A, and the two stacks are compared.  The interval claims of (b) are
    checked against the unread alphabet of sigma x.
    """
    t0 = time.time()
    checks, bad = 0, None
    cases = {"a": 0, "b": 0}
    for d in ds:
        for n in range(1, nmax + 1):
            for prefix, stack in states_cached(n, d):
                trig = triggers(prefix, d)
                q = min(trig) if trig else None
                for x in unread_letters(prefix, n):
                    if not is_trigger_of(prefix, x, d):
                        continue
                    if q is not None and x > q:
                        continue
                    # x is a d-trigger of sigma x smaller than every d-trigger of sigma
                    rest = [v for v in unread_letters(prefix, n) if v != x]
                    if q is None:                                 # case (a)
                        E = tuple(v for v in rest if v > x)
                        predicted = (E,) if E else ()
                        cases["a"] += 1
                        assert stack == ()
                    else:                                         # case (b)
                        E = tuple(v for v in rest if x < v < q)
                        if stack:
                            predicted = (tuple(sorted(E + stack[0])),) + stack[1:]
                        else:
                            predicted = (E,) if E else ()
                        cases["b"] += 1
                        above = [v for v in rest if v > x]
                        checks += 1
                        E_interval = (not E) or all(v in E for v in above
                                                    if min(E) < v < max(E))
                        head_ok = True
                        if stack:
                            head = sorted(E + stack[0])
                            head_ok = (not E or max(E) < min(stack[0])) and all(
                                v in head for v in above if head[0] < v < head[-1])
                            head_ok = head_ok and predicted[1:] == stack[1:]
                        if bad is None and not (E_interval and head_ok):
                            bad = "d=%d n=%d sigma=%s x=%d: interval claims of 2.8(b) fail" % (
                                d, n, prefix, x)
                    orders = allowed_orders(prefix + (x,), n, d)
                    vals = [v for v in rest if v > x]
                    faithful = stack_from_orders(vals, orders)
                    checks += 1
                    if bad is None and (faithful is None or faithful != predicted):
                        bad = "d=%d n=%d sigma=%s x=%d: lemma gives %s, brute force gives %s" % (
                            d, n, prefix, x, predicted, faithful)
    return result(
        "Definition 2.6 / Lemma 2.8 (stack merger)", "lem:merger",
        "%s; every legal word of [n] for n <= %d (its stack is faithful, "
        "checked in Proposition 2.10(a)) and every unread letter triggering a merger: "
        "%d instances of case (a), %d of case (b)" % (dlist(ds), nmax, cases["a"], cases["b"]),
        checks, bad is None,
        bad or "the merged stack of Lemma 2.8 equals the faithful stack obtained by "
               "brute force from the conjunction of the residual obligations, and the "
               "interval claims of (b) hold",
        time.time() - t0)


# ========================================================= Proposition 2.10

def check_scan_states_a(nmax, ds=(1, 2, 3)):
    """Proposition 2.10(a).  `The stack S(sigma) is faithful to sigma: a
    completion w of sigma satisfies the residual obligations of all d-triggers
    of sigma if and only if w|_{I_1 u ... u I_s} lies in
    Av(231)(I_1) (+) ... (+) Av(231)(I_s).'

    Compared: the language Av(231)(I_1) (+) ... (+) Av(231)(I_s) of the stack
    produced by the legal moves of Definition 2.4, versus the set of orders of
    the unread letters above the least d-trigger that satisfy every residual
    obligation, enumerated directly from the definition of a residual
    obligation (`(sigma_{j+1}...sigma_k w)|_{x>c} avoids 231').
    """
    t0 = time.time()
    checks, bad = 0, None
    for d in ds:
        for n in range(1, nmax + 1):
            for prefix, stack in states_cached(n, d):
                lhs = language(stack)
                rhs = allowed_orders(prefix, n, d)
                checks += 1
                if bad is None and lhs != rhs:
                    diff = sorted(lhs ^ rhs)[:1]
                    bad = "d=%d n=%d sigma=%s stack=%s: languages differ, e.g. %s" % (
                        d, n, prefix, stack, diff)
    return result(
        "Proposition 2.10(a) (stacks of legal words are faithful)", "prop:scan-states",
        "%s; every legal word of [n] for n <= %d, comparing the whole "
        "language of its stack with the whole set of allowed orders" % (dlist(ds), nmax),
        checks, bad is None,
        bad or "the language of S(sigma) equals the set of orders satisfying all "
               "residual obligations, for every legal word tested",
        time.time() - t0)


def check_scan_states_b(nmax, ds=(1, 2, 3)):
    """Proposition 2.10(b).  `If reading the unread letter x from sigma is
    illegal, then no beta_d-avoiding permutation has the prefix sigma x.'

    Compared: illegality of x from the scan state (Definition 2.4), versus the
    number of beta_d-avoiding permutations of [n] with prefix sigma x, counted
    by enumerating Av_n(beta_d) with permuta.  (The converse, that a legal
    letter does extend to an avoider, is part of Proposition 2.10(c).)
    """
    t0 = time.time()
    checks, bad = 0, None
    for d in ds:
        for n in range(1, nmax + 1):
            counts = prefix_counts(n, d)
            for prefix, stack in states_cached(n, d):
                for x in unread_letters(prefix, n):
                    if legal_move(prefix, stack, x, n, d) is None:
                        checks += 1
                        if bad is None and counts[prefix + (x,)] != 0:
                            bad = "d=%d n=%d sigma=%s x=%d illegal but %d avoiders " \
                                  "have that prefix" % (d, n, prefix, x,
                                                        counts[prefix + (x,)])
    return result(
        "Proposition 2.10(b) (an illegal letter kills every completion)",
        "prop:scan-states",
        "%s; every illegal (scan state, unread letter) pair with n <= %d, "
        "against the avoiders of length n listed by permuta" % (dlist(ds), nmax),
        checks, bad is None,
        bad or "every illegal letter extends no beta_d-avoider",
        time.time() - t0)


def reachable_permutations(prefix, stack, n, d):
    """R(sigma): the permutations with prefix sigma all of whose prefixes are
    legal, by depth-first search along legal moves only."""
    out = []

    def rec(pref, st):
        rest = unread_letters(pref, n)
        if not rest:
            out.append(pref)
            return
        for x in rest:
            move = legal_move(pref, st, x, n, d)
            if move is not None:
                rec(pref + (x,), move[1])

    rec(prefix, stack)
    return out


def check_scan_states_c(nmax, ds=(1, 2, 3), rmax=6):
    """Proposition 2.10(c).  `R(sigma) is the set of beta_d-avoiding
    permutations of [n] with prefix sigma; in particular R(empty) = Av_n(beta_d),
    and a word is legal if and only if it is a prefix of a beta_d-avoiding
    permutation.'

    Compared: (i) the set of words reachable from the initial state by legal
    moves, versus the set of all prefixes of the members of Av_n(beta_d) listed
    by permuta (set equality is exactly the iff of the last sentence, over all
    words with distinct letters from [n]); (ii) R(sigma) computed by
    depth-first search along legal moves, versus the avoiders with prefix
    sigma, for every legal sigma with n <= rmax and for sigma empty at every
    n <= nmax.
    """
    t0 = time.time()
    checks, bad = 0, None
    for d in ds:
        for n in range(1, nmax + 1):
            legal = {prefix for prefix, _ in states_cached(n, d)}
            av = avoiders_cached(n, d)
            prefixes = {pi[:k] for pi in av for k in range(n + 1)}
            checks += 1
            if bad is None and legal != prefixes:
                diff = sorted(legal ^ prefixes)[:1]
                bad = "d=%d n=%d: legal words != prefixes of avoiders, e.g. %s" % (
                    d, n, diff)
            byprefix = defaultdict(list)
            for pi in av:
                for k in range(n + 1):
                    byprefix[pi[:k]].append(pi)
            for prefix, stack in states_cached(n, d):
                if n > rmax and prefix != ():
                    continue
                checks += 1
                got = sorted(reachable_permutations(prefix, stack, n, d))
                if bad is None and got != sorted(byprefix[prefix]):
                    bad = "d=%d n=%d sigma=%s: R(sigma) has %d elements, %d avoiders " \
                          "have that prefix" % (d, n, prefix, len(got),
                                                len(byprefix[prefix]))
    return result(
        "Proposition 2.10(c) (R(sigma) is the set of avoiders with prefix sigma)",
        "prop:scan-states",
        "%s; the set of legal words compared with the set of prefixes of "
        "Av_n(beta_d) for every n <= %d; and R(sigma) compared with the avoiders having "
        "prefix sigma for every legal sigma when n <= %d, and for sigma empty at every "
        "n <= %d" % (dlist(ds), nmax, rmax, nmax),
        checks, bad is None,
        bad or "legal words are exactly the prefixes of avoiders, and R(sigma) is "
               "exactly the set of avoiders with prefix sigma",
        time.time() - t0)


# ============================================================= Lemma 2.11

def check_separators(nmax):
    """Lemma 2.11 (separations of the one-threshold stack).  `After a legal
    prefix has been read, let u < v be adjacent unread letters above m.  Then u
    and v lie in different intervals of the stack if and only if some letter x
    with u < x < v was read after a letter smaller than u.'

    Compared: `u and v lie in different intervals of S(sigma)', S(sigma) being
    produced by the legal moves of Definition 2.4, versus the condition read
    off the prefix alone (some read x with u < x < v whose position is preceded
    by a letter smaller than u).  Also compared: the whole stack, versus the
    increasing list of unread letters above m cut at exactly the adjacent pairs
    satisfying the condition.
    """
    t0 = time.time()
    checks, bad = 0, None
    d = 1
    for n in range(1, nmax + 1):
        for prefix, stack in states_cached(n, d):
            if not prefix:
                continue
            m = min(prefix)
            above = [v for v in unread_letters(prefix, n) if v > m]
            where = {}
            for i, I in enumerate(stack):
                for v in I:
                    where[v] = i
            cut = []
            for u, v in zip(above, above[1:]):
                witness = any(u < x < v and any(y < u for y in prefix[:i])
                              for i, x in enumerate(prefix))
                checks += 1
                if bad is None and (where[u] != where[v]) != witness:
                    bad = "n=%d sigma=%s stack=%s u=%d v=%d: different intervals=%s, " \
                          "lemma condition=%s" % (n, prefix, stack, u, v,
                                                  where[u] != where[v], witness)
                cut.append(witness)
            rebuilt, cur = [], []
            for k, v in enumerate(above):
                if k and cut[k - 1]:
                    rebuilt.append(tuple(cur))
                    cur = []
                cur.append(v)
            if cur:
                rebuilt.append(tuple(cur))
            checks += 1
            if bad is None and tuple(rebuilt) != stack:
                bad = "n=%d sigma=%s: stack %s, rebuilt from the lemma %s" % (
                    n, prefix, stack, tuple(rebuilt))
    return result(
        "Lemma 2.11 (separations of the one-threshold stack)", "lem:1342-separators",
        "d = 1; every adjacent pair of unread letters above m, for every legal word of "
        "[n] with n <= %d, plus the reconstruction of the whole stack from the prefix" % nmax,
        checks, bad is None,
        bad or "separations of S(sigma) are exactly the adjacent pairs with a witness, "
               "and the stack is recovered from the prefix alone",
        time.time() - t0)


# ========================================================= Proposition 2.13

def check_scalar_literal(nmax):
    """Proposition 2.13 (one-threshold recurrence).  W_p((l)L') is given by
    (eq:W) with the endpoint term (eq:W-endpoint), the boundary
    W_p(empty) = 1_{p=0} + sum_h W_h(nz(p-1-h)) (eq:W-boundary), and
    |Av_n(1342)| = W_n(empty) (eq:W-initial); `these equations count every
    1342-avoiding permutation exactly once'.

    Compared: W_p(L) evaluated from the displayed equations, versus the number
    of 1342-avoiding completions of an actual legal prefix with data (p, L) --
    p the number of unread letters below the current minimum m, L the list of
    interval sizes of S(sigma) -- counted by listing Av_n(1342) with permuta.
    Every legal prefix of every length is used, so every state (p, L) that
    occurs in a scan is tested.  (eq:W-initial) is tested separately at the
    empty prefix.
    """
    t0 = time.time()
    checks, bad = 0, None
    seen = set()
    for n in range(1, nmax + 1):
        counts = prefix_counts(n, 1)
        for prefix, stack in states_cached(n, 1):
            m = min(prefix) if prefix else None
            p = n if m is None else sum(1 for v in unread_letters(prefix, n) if v < m)
            L = tuple(len(I) for I in stack)
            seen.add((p, L))
            checks += 1
            if bad is None and W(p, L) != counts[prefix]:
                bad = "n=%d sigma=%s (p,L)=(%d,%s): W=%d, avoiding completions=%d" % (
                    n, prefix, p, L, W(p, L), counts[prefix])
        checks += 1
        if bad is None and W(n, ()) != len(avoiders_cached(n, 1)):
            bad = "n=%d: W_n(empty)=%d, |Av_n(1342)|=%d" % (
                n, W(n, ()), len(avoiders_cached(n, 1)))
    return result(
        "Proposition 2.13 (one-threshold recurrence)", "prop:scalar-literal",
        "d = 1; every legal prefix of every 1342-avoider of length n, for n <= %d "
        "(%d distinct states (p, L) occur), plus (eq:W-initial) for each n" % (nmax, len(seen)),
        checks, bad is None,
        bad or "W_p(L) from (eq:W)-(eq:W-boundary) equals the number of 1342-avoiding "
               "completions of every legal prefix with data (p, L), and "
               "W_n(empty) = |Av_n(1342)|",
        time.time() - t0)


# ========================================================= Proposition 2.16

def check_scalar_exponential(nmax_fib=12):
    """Proposition 2.16.  `For n >= 2, the computation of W_n(empty) reaches at
    least F_{n-1} distinct composition arguments.'

    Compared: the number of distinct compositions L occurring among the states
    (p, L) reachable from (n, empty) by the transitions of (eq:W-boundary) and
    (eq:W) -- enumerated by explicit forward search through the recurrence
    graph -- versus F_{n-1}, computed independently by the Fibonacci helper.
    The proof's stronger claim, that every composition with |L| + len(L) = n is
    reached, is checked as well, together with its counting step
    sum_s binom(n-s-1, s-1) = F_{n-1}, by enumerating those compositions.
    """
    t0 = time.time()
    checks, bad = 0, None
    detail = []
    for n in range(2, nmax_fib + 1):
        seen, frontier = set(), [(n, ())]
        comps = set()
        while frontier:
            nxt = []
            for p, L in frontier:
                if (p, L) in seen:
                    continue
                seen.add((p, L))
                comps.add(L)
                if not L:
                    nxt.extend((h, nz(p - 1 - h)) for h in range(p))
                else:
                    ell, Lp = L[0], L[1:]
                    nxt.extend((h, (ell + p - 1 - h,) + Lp) for h in range(p))
                    nxt.append((p, Lp) if ell == 1 else (p, (ell - 1,) + Lp))
                    nxt.extend((p, (a, ell - 1 - a) + Lp) for a in range(1, ell - 1))
            frontier = nxt
        fib = C.fibonacci(n - 1)
        checks += 2
        if bad is None and len(comps) < fib:
            bad = "n=%d: %d distinct compositions reached, F_{n-1}=%d" % (
                n, len(comps), fib)
        target = {L for L in compositions_upto(n) if sum(L) + len(L) == n}
        checks += 2
        if bad is None and not target <= comps:
            bad = "n=%d: some composition with |L|+len(L)=n is not reached" % n
        if bad is None and len(target) != fib:
            bad = "n=%d: %d compositions with |L|+len(L)=n, F_{n-1}=%d" % (
                n, len(target), fib)
        detail.append("n=%d: %d reached, F_%d=%d" % (n, len(comps), n - 1, fib))
    return result(
        "Proposition 2.16 (exponential literal state space)", "prop:scalar-exponential",
        "the composition arguments reachable from (n, empty) through (eq:W-boundary) "
        "and (eq:W), for 2 <= n <= %d (the asymptotic consequence itself is not "
        "finitely checkable)" % nmax_fib,
        checks, bad is None,
        bad or "distinct compositions reached >= F_{n-1} throughout; " + ", ".join(detail[:6]) + ", ...",
        time.time() - t0)


# ============================================== Theorem 2.17 / Proposition 2.19

TAILS = ((), (1,), (2,), (1, 1), (3,), (2, 1), (1, 2), (2, 3, 1))


def check_protected_tail(nmax):
    """Theorem 2.17 (protected-tail factorization), in the instance in which
    Section 2 applies it: `K_x^L(c,t) is independent of L', and
    W_p((l)L) = sum_t K_l(p,t) W_t(L) (eq:scalar-factorization).

    Compared: K_l(p,.) obtained by brute-force enumeration of the paths of the
    recurrence graph of (eq:W) that start at (p, (l)|L) and are stopped at the
    first exposure of the tail L (each summand of (eq:W) one transition, the
    endpoint term of (eq:W-endpoint) two transitions), for several tails L --
    the counts must agree; and W_p((l)L) evaluated from (eq:W) directly,
    versus sum_t K_l(p,t) W_t(L) with K from the path enumeration and W from
    (eq:W).  Also compared: the iterated form (eq:abstract-factorization),
    W_p(L) = sum_t (K_{l_1} ... K_{l_s})(p,t) G_t, with the kernel product
    assembled one factor at a time from the path-enumerated rows and
    G_t = W_t(empty).  The general statement of the theorem, for an arbitrary
    terminating recurrence on a control set and a stack, is not finitely
    checkable.
    """
    t0 = time.time()
    checks, bad = 0, None
    for total in range(1, nmax + 1):
        for ell in range(1, total + 1):
            p = total - ell
            rows = {}
            for L in TAILS:
                rows[L] = kernel_by_paths(ell, p, L)
            base = rows[()]
            for L in TAILS[1:]:
                checks += 1
                if bad is None and rows[L] != base:
                    bad = "K_%d(%d,.) depends on the tail: L=() gives %s, L=%s gives %s" % (
                        ell, p, base, L, rows[L])
            for L in compositions_upto(nmax - total):
                checks += 1
                lhs = W(p, (ell,) + L)
                rhs = sum(v * W(t, L) for t, v in base.items())
                if bad is None and lhs != rhs:
                    bad = "p=%d l=%d L=%s: W=%d, sum_t K_l(p,t) W_t(L)=%d" % (
                        p, ell, L, lhs, rhs)
                # (eq:abstract-factorization) in its iterated form:
                # W_p(L) = sum_t (K_{l_1} ... K_{l_s})(p,t) G_t, the kernel
                # product being built one factor at a time from the
                # path-enumerated rows and G_t = W_t(empty).
                full = (ell,) + L
                checks += 1
                vec = {p: 1}
                for li in full:
                    nxt = defaultdict(int)
                    for u, cu in vec.items():
                        for t, ct in kernel_by_paths(li, u, ()).items():
                            nxt[t] += cu * ct
                    vec = nxt
                prod = sum(v * W(t, ()) for t, v in vec.items())
                if bad is None and prod != W(p, full):
                    bad = "p=%d L=%s: W=%d, kernel product times G gives %d" % (
                        p, full, W(p, full), prod)
    return result(
        "Theorem 2.17 (protected-tail factorization), applied instance",
        "thm:protected-tail-principle",
        "the scalar recurrence (eq:W): stopped-path kernels K_l(p,.) for all p >= 0, "
        "l >= 1 with p + l <= %d and 8 different tails L; the factorization "
        "W_p((l)L) = sum_t K_l(p,t) W_t(L); and its iterated form "
        "(eq:abstract-factorization) W_p(L) = sum_t (K_{l_1}...K_{l_s})(p,t) G_t, "
        "for every composition L with p + l + |L| <= %d" % (nmax, nmax),
        checks, bad is None,
        bad or "the stopped-path kernel does not depend on the tail, and both the "
               "one-step and the iterated factorization hold for every state tested",
        time.time() - t0)


def check_kernel_recurrence(nmax):
    """Proposition 2.19 (scalar kernel recurrences).  K_l(p,t) satisfies
    (eq:scalar-K) with D_l(p,t) of (eq:scalar-D), and G_p satisfies
    (eq:scalar-G).

    Compared: K_l(p,.) computed from the recurrences (eq:scalar-K),
    (eq:scalar-D) with K_0(p,t) = 1_{p=t}, versus K_l(p,.) obtained by
    brute-force enumeration of stopped paths in the recurrence graph of
    (eq:W); and G_p from (eq:scalar-G) versus W_p(empty) from (eq:W-boundary),
    two different routes to the same quantity.
    """
    t0 = time.time()
    checks, bad = 0, None
    for total in range(1, nmax + 1):
        for ell in range(1, total + 1):
            p = total - ell
            checks += 1
            byrec = Krow(ell, p)
            bypath = kernel_by_paths(ell, p, ())
            if bad is None and byrec != bypath:
                bad = "K_%d(%d,.): recurrence gives %s, path enumeration gives %s" % (
                    ell, p, byrec, bypath)
    for p in range(nmax + 1):
        checks += 1
        if bad is None and G(p) != W(p, ()):
            bad = "G_%d=%d but W_%d(empty)=%d" % (p, G(p), p, W(p, ()))
    return result(
        "Proposition 2.19 (scalar kernel recurrences)", "prop:scalar-kernel-recurrence",
        "every kernel row K_l(p,.) with l >= 1 and p + l <= %d against the stopped-path "
        "enumeration, and G_p against W_p(empty) for p <= %d" % (nmax, nmax),
        checks, bad is None,
        bad or "(eq:scalar-K)/(eq:scalar-D) reproduce the stopped-path kernels, and "
               "(eq:scalar-G) reproduces W_p(empty)",
        time.time() - t0)


# ============================================================= Lemma 2.20

def check_scalar_support(nmax):
    """Lemma 2.20 (exact scalar support).  `For every p >= 0 and l >= 1,
    supp K_l(p,.) = {0, 1, ..., p}.  Moreover K_l(p,p) = C_l.'

    Compared, entry by entry: the support of the row K_l(p,.) obtained by
    brute-force enumeration of stopped paths in the recurrence graph of (eq:W),
    versus {0, ..., p}; and the diagonal entry versus the Catalan number C_l
    computed from the binomial formula.
    """
    t0 = time.time()
    checks, bad = 0, None
    for total in range(1, nmax + 1):
        for ell in range(1, total + 1):
            p = total - ell
            row = kernel_by_paths(ell, p, ())
            for t in range(0, p + ell + 2):
                checks += 1
                expect_nonzero = t <= p
                if bad is None and (row.get(t, 0) != 0) != expect_nonzero:
                    bad = "K_%d(%d,%d)=%d, support should be {0,...,%d}" % (
                        ell, p, t, row.get(t, 0), p)
            # and no terminal control at all outside {0,...,p}
            checks += 1
            if bad is None and {t for t, v in row.items() if v} != set(range(p + 1)):
                bad = "K_%d(%d,.) has support %s, not {0,...,%d}" % (
                    ell, p, sorted(t for t, v in row.items() if v), p)
            checks += 1
            if bad is None and row.get(p, 0) != catalan(ell):
                bad = "K_%d(%d,%d)=%d, C_%d=%d" % (
                    ell, p, p, row.get(p, 0), ell, catalan(ell))
    return result(
        "Lemma 2.20 (exact scalar support)", "lem:scalar-support",
        "every row K_l(p,.) with l >= 1, p >= 0 and p + l <= %d, tested entry by entry "
        "for 0 <= t <= p+l+1 and as a whole support set, against the stopped-path "
        "enumeration" % nmax,
        checks, bad is None,
        bad or "every row has support exactly {0,...,p} and diagonal entry C_l",
        time.time() - t0)


# ============================================================= Theorem 2.22

def check_scalar_algorithm(nmax_terms=10):
    """Theorem 2.22 (polynomial enumeration of 1342-avoiders).  The complexity
    statement (O(N^5) operations, O(N^3) stored integers, O(N log N) bits) is
    asymptotic and not finitely checkable; the finite content tested here is
    that the algorithm computes the right numbers.

    Compared: G_n from (eq:scalar-G), with kernel rows from (eq:scalar-K) and
    (eq:scalar-D), versus |Av_n(1342)| obtained by listing the class with
    permuta.
    """
    t0 = time.time()
    checks, bad = 0, None
    got = []
    for n in range(nmax_terms + 1):
        checks += 1
        gn = G(n)
        ref = len(C.avoiders(n, C.beta(1)))
        got.append(gn)
        if bad is None and gn != ref:
            bad = "n=%d: G_n=%d, |Av_n(1342)|=%d" % (n, gn, ref)
    return result(
        "Theorem 2.22 (polynomial enumeration of 1342-avoiders)", "thm:scalar-algorithm",
        "G_n from (eq:scalar-G) against |Av_n(1342)| from permuta for 0 <= n <= %d; "
        "the O(N^5)/O(N^3)/O(N log N) bounds are asymptotic and not finitely "
        "checkable" % nmax_terms,
        checks, bad is None,
        bad or "G_n = |Av_n(1342)| for every n tested: " + ", ".join(map(str, got)),
        time.time() - t0)


# ================================================================== interface

def run(nmax=8, verbose=False):
    """Run every Section 2 check and return the list of result dicts."""
    results = []
    jobs = [
        lambda: check_trigger(nmax),
        lambda: check_first_letter(nmax),
        lambda: check_legal_moves(nmax),
        lambda: check_scan_states_a(nmax),
        lambda: check_scan_states_b(nmax),
        lambda: check_scan_states_c(nmax, rmax=nmax),
        lambda: check_merger(nmax),
        lambda: check_separators(nmax),
        lambda: check_scalar_literal(nmax),
        lambda: check_scalar_exponential(14),
        lambda: check_protected_tail(nmax + 2),
        lambda: check_kernel_recurrence(nmax + 2),
        lambda: check_scalar_support(nmax + 2),
        lambda: check_scalar_algorithm(max(nmax, 10)),
    ]
    for job in jobs:
        res = job()
        results.append(res)
        if verbose:
            print("[%s] %-62s %6d checks %7.2fs" % (
                "ok" if res["ok"] else "FAIL", res["statement"], res["checks"],
                res["seconds"]))
            print("    scope:  " + res["scope"])
            print("    detail: " + res["detail"])
    return results


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    results = run(nmax, verbose=True)
    bad = [r for r in results if not r["ok"]]
    print("\n%d checks in %d statements, %.1f s total; %s" % (
        sum(r["checks"] for r in results), len(results),
        sum(r["seconds"] for r in results),
        "all ok" if not bad else "%d FAILED" % len(bad)))
    for r in bad:
        print("FAILED %s: %s" % (r["statement"], r["detail"]))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
