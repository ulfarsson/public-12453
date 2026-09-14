#!/usr/bin/env python3
"""firstletter_test.py -- chi-square test of the first-letter distribution.

The first letter of a uniform element of Av_n(12453) satisfies

    P[pi_1 = k] = G_{(k-1, n-k)} / G_{(n,0)},          k = 1..n,

(the top-level early-band weights at control (n,0)).  This script reads a
file of samples (one permutation per line, values 1..n) and compares the
empirical distribution with those exact probabilities, merging neighbouring
bins so that every expected count is >= 5.  It also prints a few summary
statistics of the samples.  No numpy/scipy: the regularized incomplete gamma
is implemented here.

    pypy3 firstletter_test.py --table ../tables/N150.avr --n 150 --in samples.txt
"""
import sys, os, math, argparse

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tables"))
from avr_table import AvrTable


def _gser(a, x):
    ap, s, d = a, 1.0 / a, 1.0 / a
    for _ in range(200000):
        ap += 1.0
        d *= x / ap
        s += d
        if abs(d) < abs(s) * 1e-16:
            break
    return s * math.exp(-x + a * math.log(x) - math.lgamma(a))


def _gcf(a, x):
    tiny = 1e-300
    b = x + 1.0 - a
    c = 1.0 / tiny
    d = 1.0 / b
    h = d
    for i in range(1, 200000):
        an = -1.0 * i * (i - a)
        b += 2.0
        d = an * d + b
        if abs(d) < tiny:
            d = tiny
        c = b + an / c
        if abs(c) < tiny:
            c = tiny
        d = 1.0 / d
        de = d * c
        h *= de
        if abs(de - 1.0) < 1e-16:
            break
    return math.exp(-x + a * math.log(x) - math.lgamma(a)) * h


def chi2_sf(X, dof):
    """P[chi2_dof > X]."""
    a, x = 0.5 * dof, 0.5 * X
    if x <= 0.0:
        return 1.0
    return 1.0 - _gser(a, x) if x < a + 1.0 else _gcf(a, x)


def wilson_hilferty(X, dof):
    t = (X / dof) ** (1.0 / 3.0)
    m = 1.0 - 2.0 / (9.0 * dof)
    z = (t - m) / math.sqrt(2.0 / (9.0 * dof))
    return z, 0.5 * math.erfc(z / math.sqrt(2.0))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--table", required=True)
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--in", dest="inp", required=True)
    ap.add_argument("--minexp", type=float, default=5.0)
    a = ap.parse_args()
    n = a.n
    T = AvrTable(a.table)

    obs = [0] * (n + 1)
    m = 0
    lrmin_tot = 0
    posn_tot = 0
    first_tot = 0
    with open(a.inp, "r") as fh:
        for line in fh:
            if not line.strip():
                continue
            vals = line.split()
            if len(vals) != n:
                sys.exit("line %d: length %d != n = %d" % (m + 1, len(vals), n))
            v = [int(t) for t in vals]
            obs[v[0]] += 1
            first_tot += v[0]
            m += 1
            mn = n + 1
            c = 0
            for i, x in enumerate(v):
                if x < mn:
                    mn = x
                    c += 1
                if x == n:
                    posn_tot += i + 1
            lrmin_tot += c
    if m == 0:
        sys.exit("no samples")

    tot = T.G(n, 0)
    prob = [0.0] * (n + 1)
    for k in range(1, n + 1):
        prob[k] = T.G(k - 1, n - k) / tot
    s = sum(prob[1:])
    print("samples: %d   sum of exact probabilities = %.15f (should be 1)" % (m, s))

    # merge neighbouring k into bins with expected count >= minexp
    bins, o, e, lo = [], 0, 0.0, 1
    for k in range(1, n + 1):
        o += obs[k]
        e += m * prob[k]
        if e >= a.minexp:
            bins.append((lo, k, o, e))
            o, e, lo = 0, 0.0, k + 1
    if e > 0.0 or o > 0:                      # fold the remainder into the last bin
        if bins:
            l0, _, o0, e0 = bins[-1]
            bins[-1] = (l0, n, o0 + o, e0 + e)
        else:
            bins.append((lo, n, o, e))

    X = 0.0
    for (_, _, o, e) in bins:
        X += (o - e) ** 2 / e
    dof = len(bins) - 1
    p = chi2_sf(X, dof)
    z, pz = wilson_hilferty(X, dof)
    print("bins: %d (each expected >= %.1f)   chi-square = %.4f   dof = %d   X2/dof = %.4f"
          % (len(bins), a.minexp, X, dof, X / dof))
    print("p-value (upper tail) = %.6f      Wilson-Hilferty z = %+.4f p = %.6f" % (p, z, pz))
    exp_first = sum(k * prob[k] for k in range(1, n + 1))
    print("mean first letter: empirical %.5f   exact %.5f" % (first_tot / m, exp_first))
    print("mean left-to-right minima: %.5f    mean position of n: %.5f"
          % (lrmin_tot / m, posn_tot / m))
    print("largest |obs-exp|/sqrt(exp) over bins: %.3f"
          % max(abs(o - e) / math.sqrt(e) for (_, _, o, e) in bins))
    ok = 0.001 < p < 0.999
    print("VERDICT first letter n=%d: %s" % (n, "PASS" if ok else "SUSPECT"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
