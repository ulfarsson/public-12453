#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""check_prefix.py -- consistency of two AVR1 tables of different N.

R_{l,a}(q,s) and G_{(p,q)} do not depend on N: the recurrence for a row uses
only rows of strictly smaller reduced grade, in a fixed summation order.  So a
table built at N1 must be *bit-identical* to the table built at N2 >= N1 on
every entry both of them store.  This is an end-to-end check of the layout
arithmetic as well as of the arithmetic itself.

    pypy3 check_prefix.py SMALL.avr BIG.avr
"""
import sys
from avr_table import AvrTable, slen


def main(argv):
    A = AvrTable(argv[0])
    B = AvrTable(argv[1])
    if A.N > B.N:
        A, B = B, A
    nR = nG = 0
    badR = badG = 0
    maxrel = 0.0
    worst = None
    for l in range(1, A.N + 1):
        for a in range(0, A.N - l + 1):
            for q in range(0, A.N - l - a + 1):
                ia = A.r_row_index(l, a, q)
                ib = B.r_row_index(l, a, q)
                n = slen(a, q)
                ra = A._R[ia:ia + n]
                rb = B._R[ib:ib + n]
                for s in range(n):
                    nR += 1
                    if ra[s] != rb[s]:
                        badR += 1
                        rel = abs(ra[s] - rb[s]) / abs(rb[s]) if rb[s] else 1.0
                        if rel > maxrel:
                            maxrel, worst = rel, (l, a, q, s, ra[s], rb[s])
    for p in range(0, A.N + 1):
        for q in range(0, A.N - p + 1):
            nG += 1
            if A.G(p, q) != B.G(p, q):
                badG += 1
    print("small %s (N=%d)   big %s (N=%d)" % (argv[0], A.N, argv[1], B.N))
    print("R entries compared %d, mismatches %d" % (nR, badR))
    print("G entries compared %d, mismatches %d" % (nG, badG))
    if worst:
        print("worst R mismatch rel=%.3e at %s" % (maxrel, worst))
    print("verdict %s" % ("PASS (bit-identical)" if badR == 0 and badG == 0 else "FAIL"))
    return 0 if (badR == 0 and badG == 0) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
