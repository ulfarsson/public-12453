#!/usr/bin/env python3
"""Compare two residue files, or a residue file against the exact data file
mod its prime, and report the first mismatch.

Modes (auto-detected from each file's first non-blank line):
  * both files start with "# prime P N"  -> residue-vs-residue.  Primes
    must match (comparing residues mod different primes is not meaningful);
    N may differ, comparison runs over n = 0..min(N_a, N_b).
  * one file is a residue file, the other is a plain "n value" file with
    exact (unreduced) integer values, e.g. repo/code/data/av12453_terms_*
    -- the plain file's values are reduced mod the residue file's prime
    before comparing, over n = 0..min(N, max plain n).

Exit code 0 and "MATCH" if every compared n agrees; exit code 1 and
"MISMATCH" at the first disagreement (report is not truncated to the first
one only when --all is given, in which case every disagreement is listed).

Usage:
  python3 compare_residues.py residues/123457.txt residues_old/123457.txt
  python3 compare_residues.py residues/123457.txt repo/code/data/av12453_terms_0_150.txt
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from residue_io import ResidueFormatError, read_residue_file


def is_residue_file(path: Path) -> bool:
    with path.open("r", encoding="ascii") as f:
        for raw in f:
            line = raw.strip()
            if line:
                return line.startswith("#")
    return False


def load_plain(path: Path) -> dict[int, int]:
    values: dict[int, int] = {}
    for raw in path.read_text(encoding="ascii").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        if len(parts) != 2:
            raise ValueError(f"{path}: malformed line {line!r}")
        n, v = int(parts[0]), int(parts[1])
        if n in values:
            raise ValueError(f"{path}: duplicate n={n}")
        values[n] = v
    if not values:
        raise ValueError(f"{path}: no data lines found")
    return values


def compare_residue_vs_residue(path_a: Path, path_b: Path, show_all: bool) -> int:
    prime_a, n_a, res_a = read_residue_file(path_a)
    prime_b, n_b, res_b = read_residue_file(path_b)
    if prime_a != prime_b:
        print(
            f"CANNOT COMPARE: {path_a} has prime {prime_a}, {path_b} has prime "
            f"{prime_b} (residues mod different primes are not comparable)",
            file=sys.stderr,
        )
        return 2
    limit = min(n_a, n_b)
    mismatches = [n for n in range(limit + 1) if res_a[n] != res_b[n]]
    print(f"prime={prime_a} compared n=0..{limit} ({limit + 1} values)")
    if not mismatches:
        print(f"MATCH: all {limit + 1} values agree")
        return 0
    report(path_a, path_b, prime_a, res_a, res_b, mismatches, show_all)
    return 1


def compare_residue_vs_plain(res_path: Path, plain_path: Path, show_all: bool) -> int:
    prime, n_max, residues = read_residue_file(res_path)
    plain = load_plain(plain_path)
    limit = min(n_max, max(plain))
    common_ns = [n for n in range(limit + 1) if n in plain]
    reduced = {n: plain[n] % prime for n in common_ns}
    mismatches = [n for n in common_ns if residues[n] != reduced[n]]
    print(
        f"prime={prime} compared n=0..{limit} ({len(common_ns)} values, "
        f"plain file reduced mod {prime})"
    )
    if not mismatches:
        print(f"MATCH: all {len(common_ns)} values agree")
        return 0
    a_named = {n: residues[n] for n in common_ns}
    b_named = {n: reduced[n] for n in common_ns}
    report(res_path, plain_path, prime, a_named, b_named, mismatches, show_all, indexed=True)
    return 1


def report(path_a, path_b, prime, res_a, res_b, mismatches, show_all, indexed=False):
    to_show = mismatches if show_all else mismatches[:1]
    for n in to_show:
        va = res_a[n]
        vb = res_b[n]
        print(f"MISMATCH at n={n}: {path_a} has {va}, {path_b} has {vb}  (prime={prime})")
    if not show_all and len(mismatches) > 1:
        print(f"... and {len(mismatches) - 1} more mismatch(es) (pass --all to list them)")
    print(f"TOTAL: {len(mismatches)} mismatch(es)")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("file_a", type=Path)
    ap.add_argument("file_b", type=Path)
    ap.add_argument("--all", action="store_true", help="list every mismatch, not just the first")
    args = ap.parse_args()

    a_is_res = is_residue_file(args.file_a)
    b_is_res = is_residue_file(args.file_b)

    try:
        if a_is_res and b_is_res:
            return compare_residue_vs_residue(args.file_a, args.file_b, args.all)
        if a_is_res and not b_is_res:
            return compare_residue_vs_plain(args.file_a, args.file_b, args.all)
        if b_is_res and not a_is_res:
            return compare_residue_vs_plain(args.file_b, args.file_a, args.all)
        print(
            "CANNOT COMPARE: neither file looks like a residue file "
            "(expected at least one '# prime P N' header)",
            file=sys.stderr,
        )
        return 2
    except (ResidueFormatError, ValueError, FileNotFoundError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
