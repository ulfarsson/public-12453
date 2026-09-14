#!/usr/bin/env pypy3
# -*- coding: utf-8 -*-
"""
ref.py -- independent pure-Python (pypy3) reference implementation of the
reduced d=2 recurrence for |Av_n(12453)|.

Written from the printed equations of paper/av12453_polytime.tex only
(Lemma "Exact two-threshold support" eq:support-d2, Lemma
"First-coordinate translation" eq:d2-translation, the reduced recurrence
eq:R-recurrence with its D term, and the empty-stack recurrence eq:G
transported to the reduced variables).  No repository code was read or
reused; the only repository file consulted besides the manuscript is the
certified data file av12453_terms_0_150.txt.

Equations implemented
---------------------
Reduced entry (eq:R-definition):      R_{l,a}(q,s) = K_l((a,q),(0,s)).

Support (eq:support-d2 transported through eq:d2-translation):
    supp R_{l,a}(q,.) = {0,...,q}        if a = 0,
                        {0,...,a+q-1}    if a >= 1,
so the stored row length is
    scount(a,q) = q+1   (a = 0),      a+q   (a >= 1).
(For a >= 1 and q = 0 this is a; for a = q = 0 it is 1.)

Reduced recurrence (eq:R-recurrence), for l >= 1, a,q >= 0:
    R_{l,a}(q,s) =   sum_{h=0}^{a-1}  R_{l,h}(a+q-h-1, s)          [early band]
                   + sum_{r=0}^{q-1}  R_{l+q-r-1,a}(r, s)          [last band]
                   + D_{l,a}(q,s)
                   + sum_{l1+l2=l-1, l1,l2>=1}
                     sum_{a1+a2=a,  a1,a2>=0}
                     sum_{m>=0} R_{l1,a1}(q,m) R_{l2,a2}(m,s)      [split]
    D_{1,a}(q,s) = [a = 0 and q = s],   D_{l,a}(q,s) = 2 R_{l-1,a}(q,s)  (l >= 2).
Entries outside the support are zero.  The reduced grade w = l+a+q is a
topological order: band and D terms have grade w-1, split factors grade <= w-2.

Empty-stack phase (eq:G with d = 2, T_{0,h}((p,q)) = (h, p+q-1-h),
U_h((p,q)) = (p,h), delta_h = q-1-h, and K_delta((p,h),(u,v)) =
R_{delta,p-u}(h,v) by eq:d2-translation, K_0 = identity):

    G_(p,q) = [p = q = 0]
            + sum_{h=0}^{p-1} G_(h, p+q-1-h)
            + sum_{h=0}^{q-2} sum_{u=0}^{p} sum_{v} R_{q-1-h, p-u}(h,v) G_(u,v)
            + [q >= 1] G_(p,q-1)                       (the h = q-1, delta = 0 term)

    a_n = G_(n,0)                                       (eq:answer-G).

Everything is evaluated literally: the split is the direct triple sum, with
no evaluation/interpolation scheme, memoized in increasing reduced grade.
Arithmetic is either exact Python integers or residues modulo a given prime.

CLI
---
    ref.py N [--mod P] [--dump-r FILE] [--terms FILE] [options]

--dump-r FILE writes one line "l a q s value" per NONZERO entry inside the
support, for every row with l >= 1, a,q >= 0 and l+a+q <= G (G = --max-grade,
default N), in ascending lexicographic order of the integer 4-tuple
(l, a, q, s).  Fields are separated by single spaces, lines end with "\n",
no header, no trailing blank line.  With --mod P the value is the residue in
[0,P); without it, the exact nonnegative integer.

--terms FILE writes one line "n a_n" for n = 0..N, ascending, same
conventions.
"""

import sys
import os
import time
import hashlib
import argparse
try:
    import resource
except ImportError:
    resource = None
from itertools import permutations, combinations

# ---------------------------------------------------------------- support ---

def scount(a, q):
    """Number of terminal coordinates s in the support of R_{l,a}(q,.)."""
    return q + 1 if a == 0 else a + q

# ------------------------------------------------------------ kernel phase ---

def build_R(MG, P, pad=0, progress=False):
    """Memoize R_{l,a}(q,.) for every reduced grade l+a+q <= MG.

    P = None -> exact integers, otherwise residues modulo P.
    pad > 0  -> each row carries `pad` extra terminal coordinates beyond the
                stated support; they must come out zero (support check).
    Returns (R, nmadd) where R[l][a][q] is the row (a list indexed by s) and
    nmadd is the exact number of scalar multiply-adds executed in the split.
    """
    # allocation: R[l][a] has q = 0 .. MG-l-a
    R = [None] * (MG + 2)
    for l in range(1, MG + 1):
        R[l] = [[None] * (MG - l - a + 1) for a in range(MG - l + 1)]

    nmadd = 0
    if P:
        # accumulate products without reduction while the running total is
        # provably < 2^62; then reduce the row.
        LIMIT = (1 << 62) // ((P - 1) * (P - 1)) if P > 2 else (1 << 60)
    t0 = time.time()

    for w in range(1, MG + 1):
        for l in range(1, w + 1):
            Rl = R[l]
            Rlm1 = R[l - 1] if l >= 2 else None
            for a in range(0, w - l + 1):
                q = w - l - a
                row = [0] * (scount(a, q) + pad)

                # --- early-band sum: sum_{h<a} R_{l,h}(a+q-h-1, s)
                for h in range(a):
                    src = Rl[h][a + q - h - 1]
                    for s in range(len(src)):
                        row[s] += src[s]

                # --- last-band sum: sum_{r<q} R_{l+q-r-1,a}(r, s)
                for r in range(q):
                    src = R[l + q - r - 1][a][r]
                    for s in range(len(src)):
                        row[s] += src[s]

                # --- D term
                if l == 1:
                    if a == 0:
                        row[q] += 1
                else:
                    src = Rlm1[a][q]
                    for s in range(len(src)):
                        row[s] += 2 * src[s]

                # --- split term
                if l >= 3:
                    nprod = 0
                    for l1 in range(1, l - 1):
                        l2 = l - 1 - l1
                        R1 = R[l1]
                        R2 = R[l2]
                        for a1 in range(0, a + 1):
                            a2 = a - a1
                            row1 = R1[a1][q]
                            R2a2 = R2[a2]
                            mm = len(row1)
                            lim = len(R2a2)
                            if mm > lim:
                                # entries at m >= lim are outside the support
                                # of row1 and hence zero (verified by the
                                # padded support check).
                                mm = lim
                            for m in range(mm):
                                v = row1[m]
                                if v:
                                    r2 = R2a2[m]
                                    n2 = len(r2)
                                    nmadd += n2
                                    for s in range(n2):
                                        row[s] += v * r2[s]
                            if P:
                                nprod += mm
                                if nprod > LIMIT:
                                    for s in range(len(row)):
                                        row[s] %= P
                                    nprod = 0
                if P:
                    for s in range(len(row)):
                        row[s] %= P
                Rl[a][q] = row
        if progress:
            sys.stderr.write("  grade %d/%d  madds=%d  %.1f s\n"
                             % (w, MG, nmadd, time.time() - t0))
            sys.stderr.flush()
    return R, nmadd

# -------------------------------------------------------- empty-stack phase ---

def build_G(R, N, P):
    """G[p][q] for p+q <= N, and the terms a_n = G[n][0]."""
    G = [[0] * (N - p + 1) for p in range(N + 1)]
    nops = 0
    for m in range(0, N + 1):
        for p in range(0, m + 1):
            q = m - p
            tot = 1 if m == 0 else 0
            # early-band moves: T_{0,h}((p,q)) = (h, p+q-1-h)
            for h in range(p):
                tot += G[h][m - 1 - h]
            # last-band moves: U_h((p,q)) = (p,h), delta_h = q-1-h
            for h in range(q):
                delta = q - 1 - h
                if delta == 0:
                    tot += G[p][h]          # K_0 = identity kernel
                else:
                    Rd = R[delta]
                    for a in range(0, p + 1):
                        Gu = G[p - a]
                        rrow = Rd[a][h]
                        nops += len(rrow)
                        for v in range(len(rrow)):
                            tot += rrow[v] * Gu[v]
                if P:
                    tot %= P
            if P:
                tot %= P
            G[p][q] = tot
    terms = [G[n][0] for n in range(N + 1)]
    return G, terms, nops

# ------------------------------------------------------------ brute force ---

def std(vals):
    """Standardization of a sequence of distinct values to 1..k."""
    order = sorted(range(len(vals)), key=lambda i: vals[i])
    out = [0] * len(vals)
    for rank, i in enumerate(order):
        out[i] = rank + 1
    return tuple(out)

def contains_pattern(perm, pat):
    """True iff perm contains the classical pattern pat."""
    k = len(pat)
    for idx in combinations(range(len(perm)), k):
        if std([perm[i] for i in idx]) == pat:
            return True
    return False

def brute_counts(nmax, pat=(1, 2, 4, 5, 3)):
    """|Av_n(pat)| for n = 0..nmax by direct enumeration."""
    out = []
    for n in range(nmax + 1):
        c = 0
        for perm in permutations(range(1, n + 1)):
            if not contains_pattern(perm, pat):
                c += 1
        out.append(c)
    return out

# ------------------------------------------------------------------- checks ---

def support_check(MG, P, pad=3):
    """Recompute every row of grade <= MG with `pad` extra terminal
    coordinates and verify that (i) all padded entries vanish and (ii) every
    entry inside the stated support is nonzero (the support lemma states an
    equality of sets, so this is the exact statement)."""
    R, _ = build_R(MG, P, pad=pad)
    bad_out = 0
    bad_in = 0
    nrows = 0
    for l in range(1, MG + 1):
        for a in range(0, MG - l + 1):
            for q in range(0, MG - l - a + 1):
                row = R[l][a][q]
                if row is None:
                    continue
                nrows += 1
                n = scount(a, q)
                for s in range(n, len(row)):
                    if row[s] != 0:
                        bad_out += 1
                for s in range(n):
                    if row[s] == 0:
                        bad_in += 1
    return nrows, bad_out, bad_in

def translation_check(R, MG):
    """Second-coordinate translation (eq:d2-second-translation):
    R_{l,a}(q+1,s+1) = R_{l,a}(q,s) whenever s >= a-1."""
    bad = 0
    tested = 0
    for l in range(1, MG + 1):
        for a in range(0, MG - l + 1):
            for q in range(0, MG - l - a):
                lhs_row = R[l][a][q + 1]
                rhs_row = R[l][a][q]
                for s in range(len(rhs_row)):
                    if s >= a - 1 and s + 1 < len(lhs_row):
                        tested += 1
                        if lhs_row[s + 1] != rhs_row[s]:
                            bad += 1
    return tested, bad

# ------------------------------------------------------------------- output ---

def write_dump(path, R, MG, P, keep_zeros=False):
    n_lines = 0
    h = hashlib.sha256()
    checksum = 0
    with open(path, "w") as f:
        buf = []
        ap = buf.append
        for l in range(1, MG + 1):
            for a in range(0, MG - l + 1):
                for q in range(0, MG - l - a + 1):
                    row = R[l][a][q]
                    if row is None:
                        continue
                    for s in range(scount(a, q)):
                        v = row[s]
                        if v or keep_zeros:
                            ap("%d %d %d %d %d\n" % (l, a, q, s, v))
                            n_lines += 1
                            checksum = (checksum + v) % (1 << 61)
                    if len(buf) > 65536:
                        chunk = "".join(buf)
                        h.update(chunk.encode())
                        f.write(chunk)
                        del buf[:]
                        ap = buf.append
        chunk = "".join(buf)
        h.update(chunk.encode())
        f.write(chunk)
    return n_lines, h.hexdigest(), checksum

def read_data_terms(path):
    terms = {}
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            a, b = line.split()
            terms[int(a)] = int(b)
    return terms

# --------------------------------------------------------------------- main ---

DATA_DEFAULT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "data", "av12453_terms_0_150.txt")

def main():
    ap = argparse.ArgumentParser(
        description="independent reference implementation of the reduced d=2 "
                    "recurrence for |Av_n(12453)|")
    ap.add_argument("N", type=int, help="largest n (and default largest reduced grade)")
    ap.add_argument("--mod", type=int, default=None, metavar="P",
                    help="work modulo P (default: exact integers)")
    ap.add_argument("--dump-r", default=None, metavar="FILE",
                    help="write every nonzero in-support entry as 'l a q s value'")
    ap.add_argument("--dump-all", action="store_true",
                    help="with --dump-r: also emit in-support entries whose value "
                         "is zero (a value can vanish modulo P even though the "
                         "support lemma makes it nonzero over Z)")
    ap.add_argument("--terms", default=None, metavar="FILE",
                    help="write 'n a_n' for n = 0..N")
    ap.add_argument("--max-grade", type=int, default=None,
                    help="largest reduced grade computed (default N)")
    ap.add_argument("--support-check", type=int, default=0, metavar="M",
                    help="padded support verification for every grade <= M")
    ap.add_argument("--support-pad", type=int, default=3, metavar="K",
                    help="number of extra terminal coordinates in the support "
                         "check (default 3)")
    ap.add_argument("--brute", type=int, default=0, metavar="B",
                    help="brute-force |Av_n(12453)| for n <= B and compare")
    ap.add_argument("--trans-check", action="store_true",
                    help="check the second-coordinate translation lemma")
    ap.add_argument("--check-data", nargs="?", const=DATA_DEFAULT, default=None,
                    metavar="FILE", help="compare terms against the data file")
    ap.add_argument("--progress", action="store_true", help="per-grade progress")
    ap.add_argument("--stats", default=None, metavar="FILE",
                    help="write a text/JSON-ish sidecar with timings and checksums")
    args = ap.parse_args()

    N = args.N
    P = args.mod
    MG = args.max_grade if args.max_grade is not None else N
    if MG < N - 1:
        sys.stderr.write("error: --max-grade %d is below N-1 = %d; the "
                         "empty-stack phase needs every reduced grade up to "
                         "N-1\n" % (MG, N - 1))
        return 2
    if MG < N:
        sys.stderr.write("note: --max-grade %d < N %d; grade-N rows are not "
                         "needed for the terms, only for the dump\n" % (MG, N))
    failures = []
    stats = {"N": N, "mod": P, "max_grade": MG}

    t0 = time.time()
    R, nmadd = build_R(MG, P, progress=args.progress)
    t_R = time.time() - t0
    stats["kernel_seconds"] = round(t_R, 3)
    stats["kernel_madds"] = nmadd
    sys.stderr.write("kernel phase: grades 1..%d, %d multiply-adds, %.2f s (%.3e madd/s)\n"
                     % (MG, nmadd, t_R, nmadd / t_R if t_R else 0))

    t1 = time.time()
    G, terms, nops = build_G(R, N, P)
    t_G = time.time() - t1
    stats["empty_stack_seconds"] = round(t_G, 3)
    stats["empty_stack_madds"] = nops
    sys.stderr.write("empty-stack phase: %d multiply-adds, %.2f s\n" % (nops, t_G))

    n_entries = sum(len(R[l][a][q])
                    for l in range(1, MG + 1)
                    for a in range(0, MG - l + 1)
                    for q in range(0, MG - l - a + 1))
    stats["stored_entries"] = n_entries

    # ---- checks
    if args.check_data:
        data = read_data_terms(args.check_data)
        bad = []
        nchk = 0
        for n in range(0, min(N, max(data)) + 1):
            if n in data:
                want = data[n] % P if P else data[n]
                nchk += 1
                if terms[n] != want:
                    bad.append(n)
        stats["data_check"] = "PASS(%d terms)" % nchk if not bad else "FAIL at n=%s" % bad[:5]
        sys.stderr.write("data-file check: %s\n" % stats["data_check"])
        if bad:
            failures.append("data check")

    if args.brute:
        bc = brute_counts(args.brute)
        bad = [n for n in range(args.brute + 1)
               if (bc[n] % P if P else bc[n]) != terms[n]]
        stats["brute_check"] = ("PASS(n<=%d): %s" % (args.brute, bc)) if not bad \
            else "FAIL at n=%s (brute=%s)" % (bad, bc)
        sys.stderr.write("brute-force check: %s\n" % stats["brute_check"])
        if bad:
            failures.append("brute check")

    if args.trans_check:
        tested, bad = translation_check(R, MG)
        stats["translation_check"] = "PASS(%d)" % tested if not bad else "FAIL(%d/%d)" % (bad, tested)
        sys.stderr.write("second-coordinate translation: %s\n" % stats["translation_check"])
        if bad:
            failures.append("translation check")

    if args.support_check:
        t2 = time.time()
        nrows, bad_out, bad_in = support_check(args.support_check, P,
                                               pad=args.support_pad)
        # The support lemma is an equality of sets, so over Z every in-support
        # entry must be nonzero; modulo P an entry may legitimately vanish, so
        # only the outside-support half is a failure in that case.
        if bad_out:
            stats["support_check"] = ("FAIL: %d nonzero entries outside the "
                                      "stated support" % bad_out)
        elif bad_in and P is None:
            stats["support_check"] = ("FAIL: %d zero entries inside the stated "
                                      "support (exact arithmetic)" % bad_in)
        else:
            stats["support_check"] = ("PASS: %d rows, 0 nonzero outside support, "
                                      "%d zero inside support (%s)"
                                      % (nrows, bad_in,
                                         "must be 0" if P is None
                                         else "allowed: vanishing mod P"))
        stats["support_check_seconds"] = round(time.time() - t2, 3)
        sys.stderr.write("support check (grades <= %d, pad %d): %s\n"
                         % (args.support_check, args.support_pad, stats["support_check"]))
        if bad_out or (bad_in and P is None):
            failures.append("support check")

    # ---- output
    if args.terms:
        with open(args.terms, "w") as f:
            for n in range(N + 1):
                f.write("%d %d\n" % (n, terms[n]))
        sys.stderr.write("wrote %s\n" % args.terms)

    if args.dump_r:
        t3 = time.time()
        n_lines, sha, checksum = write_dump(args.dump_r, R, MG, P, args.dump_all)
        stats["dump_lines"] = n_lines
        stats["dump_sha256"] = sha
        stats["dump_value_sum_mod_2p61"] = checksum
        stats["dump_seconds"] = round(time.time() - t3, 3)
        sys.stderr.write("wrote %s: %d lines, sha256 %s\n" % (args.dump_r, n_lines, sha))

    if resource is not None:
        stats["peak_rss_mib"] = round(
            resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024.0, 1)
    stats["total_seconds"] = round(time.time() - t0, 3)
    stats["failures"] = failures
    if args.stats:
        with open(args.stats, "w") as f:
            f.write("{\n")
            items = list(stats.items())
            for i, (k, v) in enumerate(items):
                f.write('  "%s": %s%s\n' % (k, ('"%s"' % v) if isinstance(v, str)
                                            else (str(v) if not isinstance(v, list)
                                                  else '"%s"' % v),
                                            "," if i + 1 < len(items) else ""))
            f.write("}\n")
    for k, v in stats.items():
        print("%s: %s" % (k, v))
    if failures:
        sys.stderr.write("FAILED CHECKS: %s\n" % failures)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
