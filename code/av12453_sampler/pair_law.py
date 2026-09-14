# pair_law.py -- exact law of (pi_1, pi_2) for a uniform Av_n(12453) element,
# computed from the AVR1 tables with my own reader, from eq:G directly.
#
# After pi_1 = k the control is (p,q) = (k-1, n-k) with empty stack, band0 =
# {1..k-1} (so early-band index h reads the letter h+1) and band1 = {k+1..n}
# (so last-band index r reads the letter k+r+1).  eq:G gives the weights.
import sys
from avr_mine import Avr, slen

def pair_law(T, n):
    tot = T.G(n, 0)
    P = {}
    for k in range(1, n + 1):
        p, q = k - 1, n - k
        g = T.G(p, q)
        pk = g / tot
        if pk == 0.0:
            continue
        if n == 1:
            continue
        wsum = 0.0
        row = {}
        for h in range(p):                       # early band -> letter h+1
            w = T.G(h, q + p - 1 - h)
            row[h + 1] = w; wsum += w
        for r in range(q):                       # last band  -> letter k+r+1
            l = q - 1 - r
            if l == 0:
                w = T.G(p, r)
            else:
                w = 0.0
                for c in range(p + 1):
                    A = p - c
                    rr = T.Rrow(l, A, r)
                    if rr is None: continue
                    L = min(len(rr), n - c + 1)
                    for m in range(L):
                        if rr[m]: w += rr[m]*T.G(c, m)
            row[k + r + 1] = w; wsum += w
        for j, w in row.items():
            if w > 0.0:
                P[(k, j)] = pk*(w/wsum)
        # consistency of eq:G at this control
        rel = abs(wsum - g)/g
        if rel > 3e-12:
            print("WARNING: eq:G weight sum mismatch at k=%d: %.17g vs %.17g rel=%.3e"
                  % (k, wsum, g, rel))
    return P

if __name__ == '__main__':
    T = Avr(sys.argv[1]); n = int(sys.argv[2])
    P = pair_law(T, n)
    s = sum(P.values())
    print("cells=%d  total probability=%.17g (dev %.3e)" % (len(P), s, s - 1))
    with open(sys.argv[3], 'w') as f:
        for (k, j), v in sorted(P.items()):
            f.write("%d %d %.17g\n" % (k, j, v))
