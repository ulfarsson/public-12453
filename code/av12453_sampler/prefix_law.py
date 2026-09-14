# prefix_law.py -- exact probability of a PREFIX of a uniform Av_n(12453)
# element, from my own re-implementation of the eq:H state machine plus the
# protected-tail factorization H_{(p,q)}((l)L') = sum_{c,t} R_{l,p-c}(q,t)
# H_{(c,t)}(L').  Independent of sampler_core.hpp.
import sys, itertools
from avr_mine import Avr, slen

class PL:
    def __init__(self, T, n):
        self.T, self.n = T, n
        self.memo = {}

    def H(self, p, q, L):
        if not L:
            return self.T.G(p, q)
        key = (p, q, L)
        v = self.memo.get(key)
        if v is not None: return v
        l, rest = L[0], L[1:]
        tot = 0.0
        for c in range(p + 1):
            A = p - c
            row = self.T.Rrow(l, A, q)
            if row is None: continue
            for t in range(len(row)):
                if row[t]:
                    h = self.H(c, t, rest)
                    if h: tot += row[t]*h
        self.memo[key] = tot
        return tot

    def step(self, st, v):
        """st = (U tuple, p, q, L tuple); read the letter v.  None = illegal."""
        U, p, q, L = st
        try:
            i = U.index(v)
        except ValueError:
            return None
        U2 = U[:i] + U[i+1:]
        if i < p:                                   # early band
            h = i
            return (U2, h, q + p - 1 - h, L)
        if i < p + q:                               # last band
            r = i - p
            delta = q - 1 - r
            if L:
                L2 = (L[0] + delta,) + L[1:]
            else:
                L2 = ((delta,) if delta > 0 else ())
            return (U2, p, r, L2)
        if not L:
            return None
        j = i - (p + q) + 1                          # local rank inside I_1
        l = L[0]
        if j > l:
            return None                              # deeper block: not readable
        if j == 1 or j == l:                         # endpoint
            L2 = ((l - 1,) + L[1:]) if l > 1 else L[1:]
            return (U2, p, q, L2)
        return (U2, p, q, (j - 1, l - j) + L[1:])    # interior split

    def start(self):
        n = self.n
        return (tuple(range(1, n + 1)), n, 0, ())

    def prefix_count(self, w):
        st = self.start()
        for v in w:
            st = self.step(st, v)
            if st is None: return 0.0
        return self.H(st[1], st[2], st[3])

if __name__ == '__main__':
    T = Avr(sys.argv[1]); n = int(sys.argv[2]); m = int(sys.argv[3])
    pl = PL(T, n)
    tot = T.G(n, 0)
    # sanity: the empty prefix and all length-1 prefixes
    s = sum(pl.prefix_count((k,)) for k in range(1, n + 1))
    print("n=%d: sum of length-1 prefix counts = %.17g, G(n,0) = %.17g, rel %.3e"
          % (n, s, tot, abs(s - tot)/tot))
    out = {}
    for w in itertools.permutations(range(1, n + 1), m):
        c = pl.prefix_count(w)
        if c > 0: out[w] = c/tot
    s2 = sum(out.values())
    print("length-%d prefixes with positive count: %d, total probability %.17g (dev %.3e)"
          % (m, len(out), s2, s2 - 1))
    with open(sys.argv[4], 'w') as f:
        for w, pr in sorted(out.items()):
            f.write("%s %.17g\n" % (' '.join(map(str, w)), pr))
