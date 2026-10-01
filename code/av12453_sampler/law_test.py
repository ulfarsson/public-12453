#!/usr/bin/env python3
"""law_test.py -- chi-square test of sampled prefixes against an exact prefix law.

    pypy3 law_test.py LAW.txt SAMPLES.txt [--minexp 5]

LAW.txt is written by pair_law.py (lines "k j probability": the law of the
first two letters) or by prefix_law.py (lines "w_1 ... w_m probability": the
law of the first m letters); m is read off the file.  SAMPLES.txt holds one
permutation per line (values 1..n), as written by the sampler.  The test

  * fails at once if some sample begins with a prefix of probability zero
    (such a prefix is not the prefix of any avoider);
  * otherwise merges the prefixes, in decreasing order of probability, into
    bins of expected count at least --minexp and prints the chi-square
    statistic, its degrees of freedom and the upper-tail p-value.

Exit status 0 iff the law sums to 1 within 1e-9 and 0.001 < p < 0.999, the
verdict used by firstletter_test.py.
"""
import sys
import argparse

from firstletter_test import chi2_sf


def read_law(path):
    law = {}
    m = None
    with open(path) as f:
        for line in f:
            fl = line.split()
            if not fl:
                continue
            key = tuple(int(x) for x in fl[:-1])
            if m is None:
                m = len(key)
            elif len(key) != m:
                sys.exit("%s: prefixes of different lengths" % path)
            law[key] = float(fl[-1])
    return law, m


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("law")
    ap.add_argument("samples")
    ap.add_argument("--minexp", type=float, default=5.0)
    args = ap.parse_args(argv)

    law, m = read_law(args.law)
    total = sum(law.values())
    obs = {}
    M = 0
    impossible = 0
    with open(args.samples) as f:
        for line in f:
            fl = line.split()
            if not fl:
                continue
            key = tuple(int(x) for x in fl[:m])
            M += 1
            if key not in law or law[key] <= 0.0:
                impossible += 1
                continue
            obs[key] = obs.get(key, 0) + 1
    print("law              %s (prefix length %d, %d prefixes, total probability %.15f)"
          % (args.law, m, len(law), total))
    print("samples          %s (%d)" % (args.samples, M))
    if M == 0:
        sys.exit("no samples")
    if impossible:
        print("samples with a prefix of probability zero: %d" % impossible)
        print("VERDICT: FAIL")
        return 1

    bins = []
    o, e = 0, 0.0
    for key in sorted(law, key=lambda k: -law[k]):
        o += obs.get(key, 0)
        e += M * law[key]
        if e >= args.minexp:
            bins.append((o, e))
            o, e = 0, 0.0
    if o or e > 0.0:                      # fold the remainder into the last bin
        if bins:
            o0, e0 = bins[-1]
            bins[-1] = (o0 + o, e0 + e)
        else:
            bins.append((o, e))
    X = sum((o - e) ** 2 / e for (o, e) in bins)
    dof = len(bins) - 1
    p = chi2_sf(X, dof) if dof > 0 else 1.0
    print("bins             %d (each expected >= %g)" % (len(bins), args.minexp))
    print("chi-square       %.4f on %d dof (X2/dof = %.4f)" % (X, dof, X / dof if dof else 0.0))
    print("p-value          %.6f" % p)
    ok = abs(total - 1.0) < 1e-9 and 0.001 < p < 0.999
    print("VERDICT: %s" % ("PASS" if ok else "SUSPECT"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
