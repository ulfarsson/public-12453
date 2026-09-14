#!/usr/bin/env python3
"""check_ratios.py -- the probabilities a sampler test needs must not depend
on whether the table is scaled.

    pypy3 check_ratios.py SCALED.avr UNSCALED.avr [--n N]

Compares, for n = --n (default: the table N):
  * the exact first-letter law  P[pi_1 = k] = G_{(k-1,n-k)} / G_{(n,0)},
  * a sample of kernel ratios   R_{l,a}(q,s) / R_{l',a'}(q',s')
computed through AvrTable.g_ratio / .r_ratio from both tables.  They should
agree to the last bit or so; a mismatch means the grade factors are wrong.
"""
import sys
from avr_table import AvrTable


def main(argv):
    S = AvrTable(argv[0])
    U = AvrTable(argv[1])
    n = int(argv[argv.index("--n") + 1]) if "--n" in argv else min(S.N, U.N)
    worst, where = 0.0, None
    tot_s = tot_u = 0.0
    for k in range(1, n + 1):
        ps = S.g_ratio(k - 1, n - k, n, 0)
        pu = U.g_ratio(k - 1, n - k, n, 0)
        tot_s += ps
        tot_u += pu
        if pu:
            rel = abs(ps - pu) / pu
            if rel > worst:
                worst, where = rel, k
    print("first-letter law at n = %d" % n)
    print("  sum of probabilities  scaled %.17g   unscaled %.17g" % (tot_s, tot_u))
    print("  max relative difference %.3e at k = %s" % (worst, where))
    ok = worst < 1e-14 and abs(tot_s - 1.0) < 1e-9

    # a deterministic spread of kernel ratios across grades
    worst2, where2 = 0.0, None
    cnt = 0
    st = 12345
    for _ in range(4000):
        vals = []
        for _ in range(2):
            st = (st * 6364136223846793005 + 1442695040888963407) % (1 << 64)
            l = 1 + (st >> 13) % max(1, n // 2)
            st = (st * 6364136223846793005 + 1442695040888963407) % (1 << 64)
            a = (st >> 17) % max(1, n - l + 1)
            st = (st * 6364136223846793005 + 1442695040888963407) % (1 << 64)
            q = (st >> 19) % max(1, n - l - a + 1)
            st = (st * 6364136223846793005 + 1442695040888963407) % (1 << 64)
            s = (st >> 23) % (q + 1 if a == 0 else a + q)
            vals.append((l, a, q, s))
        (l1, a1, q1, s1), (l2, a2, q2, s2) = vals
        du = U.R(l2, a2, q2, s2)
        if du == 0.0:
            continue
        rs = S.r_ratio(l1, a1, q1, s1, l2, a2, q2, s2)
        ru = U.r_ratio(l1, a1, q1, s1, l2, a2, q2, s2)
        cnt += 1
        if ru:
            rel = abs(rs - ru) / abs(ru)
            if rel > worst2:
                worst2, where2 = rel, (vals[0], vals[1])
    print("kernel ratios: %d pairs compared" % cnt)
    print("  max relative difference %.3e at %s" % (worst2, where2))
    ok = ok and worst2 < 1e-14
    print("verdict %s" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
