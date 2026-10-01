#!/usr/bin/env python3
"""check_r.py -- compare an AVR1 or AVR2 table against an exact dump of pyref/ref.py.

    ref.py N --dump-r FILE      writes "l a q s value" for every NONZERO
                                in-support entry, exact integers.

Usage:  pypy3 check_r.py TABLE.avr DUMP.txt [--top K] [--tol 1e-9]

Reports: the number of entries compared, the maximum relative error and where
it occurs, and whether the two index sets of nonzero entries coincide
(entries nonzero in the dump but zero in the table, and vice versa).

The stored doubles are unscaled exactly (R_exact(): the stored value times the
exact power of two of an AVR2 table) and every relative error is formed in
rational arithmetic, so a scaled and an unscaled table of the same N give the
same report.  Exit status 0 iff the maximum relative error is below --tol AND
the index sets of nonzero entries coincide.
"""
import sys
from avr_table import AvrTable


def main(argv):
    table_path, dump_path = argv[0], argv[1]
    top = 5
    tol = 1e-9
    if "--top" in argv:
        top = int(argv[argv.index("--top") + 1])
    if "--tol" in argv:
        tol = float(argv[argv.index("--tol") + 1])
    T = AvrTable(table_path)
    seen = {}
    n = 0
    maxrel = 0.0
    where = None
    worst = []
    only_dump = 0          # nonzero in exact dump, zero in the table
    grade_over = 0
    with open(dump_path) as f:
        for line in f:
            if not line.strip():
                continue
            fl = line.split()
            l, a, q, s = int(fl[0]), int(fl[1]), int(fl[2]), int(fl[3])
            exact = int(fl[4])
            if l + a + q > T.N:
                grade_over += 1
                continue
            got = T.R_exact(l, a, q, s)          # unscaled, exact
            seen[(l, a, q, s)] = True
            n += 1
            if exact == 0:
                continue
            if got == 0:
                only_dump += 1
            rel = float(abs(got - exact) / abs(exact))
            if rel > maxrel:
                maxrel, where = rel, (l, a, q, s)
            worst.append((rel, l, a, q, s, T.R(l, a, q, s), exact))
            if len(worst) > 4000:
                worst.sort(reverse=True)
                del worst[top:]
    # the other direction: entries stored (in support) but absent from the dump
    only_table = 0
    stored = 0
    examples = []
    for (l, a, q, s, v) in T.iter_r():
        stored += 1
        if (l, a, q, s) not in seen:
            if v != 0.0:
                only_table += 1
                if len(examples) < 5:
                    examples.append((l, a, q, s, v))
    worst.sort(reverse=True)
    supports_agree = (only_dump == 0 and only_table == 0 and n == stored)
    ok = supports_agree and maxrel < tol
    print("table            %s (N=%d, %s)" % (table_path, T.N,
          "AVR2, stored = true * 2^{-%d*grade}" % T.scale if T.scale else "AVR1, unscaled"))
    print("dump             %s" % dump_path)
    print("entries compared %d" % n)
    print("stored entries   %d" % stored)
    print("dump lines with grade > N (skipped): %d" % grade_over)
    print("max relative err %.6e  at (l,a,q,s)=%s   (tolerance %g)" % (maxrel, where, tol))
    print("nonzero in dump but 0.0 in table: %d" % only_dump)
    print("nonzero in table but absent from dump: %d %s" % (only_table, examples))
    print("index sets of nonzero entries coincide: %s" % ("YES" if supports_agree else "NO"))
    print("verdict          %s" % ("PASS" if ok else "FAIL"))
    print("worst %d:" % top)
    for r in worst[:top]:
        print("  rel=%.4e  R(%d,%d,%d,%d): stored %.17g   exact = %d" %
              (r[0], r[1], r[2], r[3], r[4], r[5], r[6]))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
