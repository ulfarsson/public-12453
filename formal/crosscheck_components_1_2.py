"""Independent brute-force cross-check of the Lean development (0-based, permuta-style).

Everything here is written from scratch from the PAPER's definitions, not from the
Lean source; the Lean definitions are re-implemented separately (functions prefixed
`lean_`) so the two can be compared.
"""
from itertools import permutations, combinations
import random

# ---------- reference (paper) notions, 0-based ----------

def order_iso(u, v):
    """u and v have the same relative order at every pair of positions."""
    if len(u) != len(v):
        return False
    n = len(u)
    return all((u[i] < u[j]) == (v[i] < v[j]) for i in range(n) for j in range(n))

def contains(w, pat):
    """some subsequence of w is order-isomorphic to pat"""
    k = len(pat)
    for idx in combinations(range(len(w)), k):
        if order_iso([w[i] for i in idx], pat):
            return True
    return False

def avoids(w, pat):
    return not contains(w, pat)

PAT231 = [1, 2, 0]                      # 231, 0-based

def iota(d):
    return list(range(d))               # 0,...,d-1

def beta(d):
    return iota(d) + [d + 1, d + 2, d]  # iota_d (+) 231

# ---------- part 3a: counts of avoiders ----------

def count_avoiders(pat, nmax):
    out = []
    for n in range(nmax + 1):
        c = 0
        for p in permutations(range(n)):
            if avoids(list(p), pat):
                c += 1
        out.append(c)
    return out

EXPECT_1342  = [1, 1, 2, 6, 23, 103, 512, 2740]
EXPECT_12453 = [1, 1, 2, 6, 24, 119, 694, 4581]

fails = []

b1, b2 = beta(1), beta(2)
assert b1 == [0, 2, 3, 1], b1
assert b2 == [0, 1, 3, 4, 2], b2
# order-type check against the paper's 1-based words 1342 and 12453
assert order_iso(b1, [1, 3, 4, 2]), "beta 1 is not the order type of 1342"
assert order_iso(b2, [1, 2, 4, 5, 3]), "beta 2 is not the order type of 12453"

got1 = count_avoiders(b1, 7)
got2 = count_avoiders(b2, 7)
print("Av(beta 1)=Av(1342) n=0..7:", got1, "OK" if got1 == EXPECT_1342 else "MISMATCH")
print("Av(beta 2)=Av(12453) n=0..7:", got2, "OK" if got2 == EXPECT_12453 else "MISMATCH")
if got1 != EXPECT_1342: fails.append("1342 counts")
if got2 != EXPECT_12453: fails.append("12453 counts")

# ---------- part 3b: standardize ----------

def lean_standardize(w):
    """Av12453.standardize: w.map (fun x => (w.filter (. < x)).length)"""
    return [len([y for y in w if y < x]) for x in w]

def rank_map(w):
    """textbook st: replace smallest by 0, next by 1, ... (requires distinct entries)"""
    s = sorted(w)
    return [s.index(x) for x in w]

random.seed(20260904)
bad_std = 0
for _ in range(4000):
    n = random.randint(0, 9)
    w = random.sample(range(0, 40), n)          # distinct entries
    if lean_standardize(w) != rank_map(w):
        bad_std += 1
        if bad_std < 4: print("  STD MISMATCH", w, lean_standardize(w), rank_map(w))
# also: st(w) is a permutation of 0..n-1, and order-isomorphic to w
bad_perm = 0
for _ in range(2000):
    n = random.randint(0, 8)
    w = random.sample(range(0, 40), n)
    st = lean_standardize(w)
    if sorted(st) != list(range(n)) or not order_iso(w, st):
        bad_perm += 1
print("standardize vs rank map on 4000 random distinct-entry words:",
      "OK" if bad_std == 0 else f"{bad_std} MISMATCHES")
print("standardize is a permutation of 0..n-1 and order-preserving (2000 words):",
      "OK" if bad_perm == 0 else f"{bad_perm} FAILURES")
if bad_std or bad_perm: fails.append("standardize")

# words WITH repeats: the Lean def is still total; check it is NOT claimed order-iso there
w = [4, 1, 4, 0]
print("  (repeats) lean_standardize([4,1,4,0]) =", lean_standardize(w),
      "; order_iso with source:", order_iso(w, lean_standardize(w)))

# ---------- part 3c: index characterisations ----------

def contains_231_idx(w):
    n = len(w)
    return any(w[k] < w[i] < w[j]
               for i in range(n) for j in range(i+1, n) for k in range(j+1, n))

def contains_12453_idx(w):
    n = len(w)
    for i1 in range(n):
        for i2 in range(i1+1, n):
            for j in range(i2+1, n):
                for k in range(j+1, n):
                    for l in range(k+1, n):
                        if w[i1] < w[i2] < w[l] < w[j] < w[k]:
                            return True
    return False

def contains_beta_idx(w, d):
    n = len(w)
    for ps in combinations(range(n), d):
        if any(w[ps[a]] >= w[ps[a+1]] for a in range(d-1)):
            continue
        lo = ps[-1] if d else -1
        for j in range(lo+1, n):
            for k in range(j+1, n):
                for l in range(k+1, n):
                    if (d == 0 or w[ps[-1]] < w[l]) and w[l] < w[j] < w[k]:
                        return True
    return False

bad_idx = 0
for n in range(0, 8):
    for p in permutations(range(n)):
        w = list(p)
        if contains(w, PAT231) != contains_231_idx(w): bad_idx += 1
for n in range(0, 8):
    for p in permutations(range(n)):
        w = list(p)
        if contains(w, b2) != contains_12453_idx(w): bad_idx += 1
        for d in (0, 1, 2, 3):
            if contains(w, beta(d)) != contains_beta_idx(w, d): bad_idx += 1
print("index characterisations contains_231_iff / contains_beta_iff / contains_12453_iff, n<=7:",
      "OK" if bad_idx == 0 else f"{bad_idx} MISMATCHES")
if bad_idx: fails.append("index characterisations")

# ---------- part 3d: Lemma 2.1 (trigger lemma) ----------

def is_trigger_at(w, d, j):
    """position j ends an increasing d-subsequence"""
    if not (0 <= j < len(w)):
        return False
    if d == 0:
        return False          # the paper's d-subsequences are nonempty; Lean needs 1 <= d
    for ps in combinations(range(j), d - 1):
        vals = [w[i] for i in ps] + [w[j]]
        if all(vals[a] < vals[a+1] for a in range(len(vals)-1)):
            return True
    return False

def trigger_rhs(w, d):
    for j in range(len(w)):
        if is_trigger_at(w, d, j):
            tail = [x for x in w[j+1:] if x > w[j]]
            if contains(tail, PAT231):
                return False
    return True

def trigger_rhs_standardized(w, d):
    for j in range(len(w)):
        if is_trigger_at(w, d, j):
            tail = [x for x in w[j+1:] if x > w[j]]
            if contains(lean_standardize(tail), PAT231):
                return False
    return True

bad_t = []
for d in (1, 2, 3):
    for n in range(0, 7):
        for p in permutations(range(n)):
            w = list(p)
            lhs = avoids(w, beta(d))
            if lhs != trigger_rhs(w, d) or lhs != trigger_rhs_standardized(w, d):
                bad_t.append((d, w))
print("Lemma 2.1 (d=1,2,3), all permutations n<=6, plain and standardized forms:",
      "OK" if not bad_t else f"{len(bad_t)} FAILURES e.g. {bad_t[:3]}")
if bad_t: fails.append("Lemma 2.1")

# d=1 specialisation: every position is a 1-trigger
bad_t1 = 0
for n in range(0, 7):
    for p in permutations(range(n)):
        w = list(p)
        if any(is_trigger_at(w, 1, j) != (j < len(w)) for j in range(len(w) + 2)):
            bad_t1 += 1
print("isTriggerAt_one_iff (every position is a 1-trigger), n<=6:",
      "OK" if bad_t1 == 0 else f"{bad_t1} FAILURES")
if bad_t1: fails.append("isTriggerAt_one_iff")

# d=0 would make the lemma FALSE -- justifies the 1 <= d hypothesis
d0_bad = [list(p) for n in range(5) for p in permutations(range(n))
          if avoids(list(p), beta(0)) != trigger_rhs(list(p), 0)]
print("  sanity: with d = 0 the equivalence fails for", len(d0_bad),
      "permutations with n<=4 (so the `1 <= d` hypothesis is needed)")

# ---------- part 3e: Lemma 2.2 (first-letter lemma) ----------

def below_before_above(x, w):
    return all(not (i > j) for i in range(len(w)) for j in range(len(w))
               if w[i] < x and x < w[j]) and \
           all(i < j for i in range(len(w)) for j in range(len(w))
               if w[i] < x and x < w[j])

def lean_rank(x, w):
    return len([y for y in w if y < x])

bad_fl = []
bad_card = []
for n in range(1, 8):                      # word x::w of length n, n <= 7
    for p in permutations(range(n)):
        x, w = p[0], list(p[1:])
        lhs = avoids([x] + w, PAT231)
        lo = [y for y in w if y < x]
        hi = [y for y in w if y > x]
        rhs = below_before_above(x, w) and avoids(lo, PAT231) and avoids(hi, PAT231)
        if lhs != rhs:
            bad_fl.append((x, w))
        # "in that order": w is literally lower ++ upper
        if below_before_above(x, w) and w != lo + hi:
            bad_fl.append(("append", x, w))
        # cardinality corollary; paper's r = rank + 1, ell = len(x::w)
        ell = n
        r = len([y for y in [x] + w if y <= x])
        if not (r == lean_rank(x, w) + 1 and len(lo) == r - 1 and len(hi) == ell - r
                and len(lo) == lean_rank(x, w) and len(hi) == ell - 1 - lean_rank(x, w)):
            bad_card.append((x, w))
print("Lemma 2.2 (first-letter lemma) + `in that order`, all words x::w with n<=7:",
      "OK" if not bad_fl else f"{len(bad_fl)} FAILURES e.g. {bad_fl[:3]}")
print("cardinality corollary r-1 / ell-r == rank / ell-1-rank, all words x::w with n<=7:",
      "OK" if not bad_card else f"{len(bad_card)} FAILURES e.g. {bad_card[:3]}")
if bad_fl: fails.append("Lemma 2.2")
if bad_card: fails.append("Lemma 2.2 cardinality")

# Nodup is needed: the Lean counterexample
x, w = 4, [1, 4, 0]
lo = [y for y in w if y < x]; hi = [y for y in w if y > x]
print("  Nodup counterexample x=4, w=[1,4,0]: contains231(4140) =",
      contains([x]+w, PAT231), "; rhs =",
      below_before_above(x, w) and avoids(lo, PAT231) and avoids(hi, PAT231))

# ---------- part 3f: general-d family, Lemma 2.1 applied recursively ----------
print()
print("SUMMARY:", "ALL CHECKS PASS" if not fails else "FAILURES: " + ", ".join(fails))
