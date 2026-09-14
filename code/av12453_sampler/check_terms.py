#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""check_terms.py -- compare an AVR1 table's G(n,0) with the exact terms.

    python3 check_terms.py TABLE.avr [--terms FILE] [--tol 1e-11] [--top K]

FILE defaults to repo/code/data/av12453_terms_0_300.txt (lines "n a_n").
Prints the maximum relative error |G(n,0) - a_n| / a_n over all n <= N and the
worst offenders.  Exit status 0 iff every relative error is below --tol.
"""
import os
import sys
import argparse
from avr_table import AvrTable

DEFAULT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data", "av12453_terms_0_300.txt")


def read_terms(path):
    out = {}
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            a, b = line.split()
            out[int(a)] = int(b)
    return out


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("table")
    ap.add_argument("--terms", default=DEFAULT)
    ap.add_argument("--tol", type=float, default=1e-11)
    ap.add_argument("--top", type=int, default=5)
    ap.add_argument("--mmap", action="store_true")
    args = ap.parse_args(argv)

    T = AvrTable(args.table, use_mmap=args.mmap)
    exact = read_terms(args.terms)
    rows = []
    maxrel = 0.0
    where = None
    for n in range(0, T.N + 1):
        if n not in exact:
            continue
        got = T.G(n, 0)
        e = exact[n]
        rel = 0.0 if e == 0 else abs(got - e) / e
        rows.append((rel, n, got, e))
        if rel > maxrel:
            maxrel, where = rel, n
    rows.sort(reverse=True)
    print("table            %s (N=%d)" % (args.table, T.N))
    print("terms            %s" % args.terms)
    print("n compared       %d  (n = 0..%d)" % (len(rows), T.N))
    print("max relative err %.6e  at n = %s   (tolerance %g)" % (maxrel, where, args.tol))
    print("verdict          %s" % ("PASS" if maxrel < args.tol else "FAIL"))
    for r in rows[:args.top]:
        print("  n=%3d rel=%.4e  table=%.17g" % (r[1], r[0], r[2]))
    return 0 if maxrel < args.tol else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
