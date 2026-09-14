#!/usr/bin/env python3
"""Exhaustive checks of the paper's statements for permutations of length <= 8.

Every numbered statement of the paper that has finite content is checked by
comparing the paper's construction or displayed formula with a brute-force
computation from the definitions, using permuta for the permutations and
pattern containment.  The checks are organised by section in checks/sec2.py
(Section 2), checks/sec345.py (Sections 3-5) and checks/sec678.py (Sections
6-8 and 10); checks/common.py holds the shared brute-force helpers.  Nothing
here uses the fast implementations in code/.

    pypy3 av12453_exhaustive_checks.py [--nmax 8] [--verbose]

Prints one line per statement and exits with status 1 if any check fails.
"""
import argparse
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from checks import sec2, sec345, sec678  # noqa: E402


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--nmax", type=int, default=8, help="largest permutation length checked (default 8)")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args(argv)
    t0 = time.time()
    results = []
    for module in (sec2, sec345, sec678):
        results.extend(module.run(nmax=args.nmax, verbose=args.verbose))
    width = max(len(r["statement"]) for r in results)
    print(f"{'statement':<{width}}  {'checks':>9}  {'time':>6}  result")
    failures = 0
    total_checks = 0
    for r in results:
        total_checks += r.get("checks", 0)
        status = "ok" if r["ok"] else "FAIL"
        if not r["ok"]:
            failures += 1
        print(f"{r['statement']:<{width}}  {r.get('checks', 0):>9}  {r.get('seconds', 0.0):>5.1f}s  {status}  [{r['scope']}]")
        if args.verbose or not r["ok"]:
            print(f"{'':<{width}}  {r.get('detail', '')}")
    print(f"\n{len(results)} statements, {total_checks} comparisons, {failures} failures, {time.time() - t0:.0f}s total")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
