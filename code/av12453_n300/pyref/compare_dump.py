#!/usr/bin/env pypy3
"""compare_dump.py A.txt B.txt [--mod P] [--max-grade G]

Compare two R-table dumps in the ref.py format

    l a q s value          (one entry per line, single-space separated)

The comparison is by (l,a,q,s) key.  A key present in one file and absent
from the other is treated as value 0 (ref.py omits zero values by default,
another engine may or may not emit them), so the two conventions compare
equal.  With --mod P the values of both files are reduced mod P first.
With --max-grade G only keys with l+a+q <= G are compared, which lets a
dump produced up to one grade bound be compared with a dump produced up to
a larger one.

Exit status 0 iff the two dumps agree.
"""
import sys

def load(path, P=None, G=None):
    d = {}
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line[0] == '#':
                continue
            fs = line.split()
            l, a, q, s, v = int(fs[0]), int(fs[1]), int(fs[2]), int(fs[3]), int(fs[4])
            if G is not None and l + a + q > G:
                continue
            if P:
                v %= P
            if v:
                d[(l, a, q, s)] = v
    return d

def main():
    args = [x for x in sys.argv[1:]]
    P = None
    G = None
    if "--mod" in args:
        i = args.index("--mod"); P = int(args[i+1]); del args[i:i+2]
    if "--max-grade" in args:
        i = args.index("--max-grade"); G = int(args[i+1]); del args[i:i+2]
    A = load(args[0], P, G)
    B = load(args[1], P, G)
    keys = set(A) | set(B)
    bad = [k for k in keys if A.get(k, 0) != B.get(k, 0)]
    bad.sort()
    print("%s: %d nonzero entries" % (args[0], len(A)))
    print("%s: %d nonzero entries" % (args[1], len(B)))
    print("compared keys: %d, mismatches: %d" % (len(keys), len(bad)))
    for k in bad[:20]:
        print("  l=%d a=%d q=%d s=%d : %s vs %s" % (k + (A.get(k, 0), B.get(k, 0))))
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main())
