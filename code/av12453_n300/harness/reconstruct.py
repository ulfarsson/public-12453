#!/usr/bin/env python3
"""Reconstruct exact a_n = |Av_n(12453)| terms from prime-residue files.

Pipeline:
  1. Parse every residue file in --residues-dir (or given explicitly) with
     residue_io.read_residue_file; every file must have the same N (equal
     to --n) and a distinct prime.
  2. Verify residues for n <= 150 against the certified data file
     (--data-file, default repo/code/data/av12453_terms_0_150.txt),
     reduced modulo each prime -- for EVERY prime supplied, not just the
     ones later chosen as primary.
  3. Compute B_N = sum_m C(N,m)^2 |Av_m(1342)| exactly (bona_bound.py).
  4. Choose the smallest set of primes (by count) whose product exceeds
     B_N: sort available primes descending and take a prefix -- this is
     optimal because, to reach a given product with the fewest factors,
     using the k largest available primes maximizes the achievable product
     for that k, so if any k-subset exceeds the bound the largest-k-subset
     does too, and conversely.  These are the "primary" primes; every other
     supplied prime is "withheld" (used only as an independent check).
  5. CRT-reconstruct a_n for n=0..N from the primary primes (incremental /
     Garner-style reconstruction), and check 0 <= a_n <= B_n (per-n bound,
     tighter than B_N) for every n.
  6. Check every withheld prime's residues agree with the reconstructed
     values at every n.
  7. Check the reconstructed n<=150 prefix matches the data file exactly
     (belt-and-suspenders on top of step 2's modular check).
  8. Write terms_0_N.txt ("n a_n" lines) and print the summary line:
     "reconstructed=.. primary=.. withheld=.. bound_bits=.. product_bits=.."

Usage:
  pypy3 reconstruct.py --residues-dir residues --n 300 --output terms_0_300.txt
  pypy3 reconstruct.py FILE1 FILE2 ... --n 150 --output terms_0_150.txt
"""

from __future__ import annotations

import argparse
import hashlib
import os
import sys
from pathlib import Path

from bona_bound import injection_bounds
from residue_io import ResidueFormatError, read_residue_file

DEFAULT_DATA_FILE = Path(__file__).resolve().parents[2] / "data" / "av12453_terms_0_150.txt"
DEFAULT_DATA_SHA256 = (
    "f5ab4017ec65a661d8fbcd84d2f7893afe5e2c695dd082ace58399f7960340fc"
)


def read_known_prefix(path: Path, expect_sha256: str | None) -> list[int]:
    raw = path.read_bytes()
    if expect_sha256 is not None:
        got = hashlib.sha256(raw).hexdigest()
        if got != expect_sha256:
            raise ArithmeticError(
                f"{path}: sha256 {got} does not match expected {expect_sha256} "
                "-- refusing to trust a possibly-altered data file "
                "(pass --skip-hash-check to override)"
            )
    known: list[int] = []
    for line in raw.decode("ascii").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        n_text, v_text = line.split()
        n = int(n_text)
        if n != len(known):
            raise ValueError(f"{path}: nonconsecutive degree at line {n_text}")
        known.append(int(v_text))
    return known


def find_residue_files(args: argparse.Namespace) -> list[Path]:
    if args.residue_files:
        return [Path(p) for p in args.residue_files]
    if args.residues_dir is None:
        raise SystemExit("must give either residue files or --residues-dir")
    files = sorted(Path(args.residues_dir).glob("*.txt"))
    if not files:
        raise SystemExit(f"no *.txt residue files found in {args.residues_dir}")
    return files


def load_all(files: list[Path], expected_n: int) -> list[tuple[int, list[int]]]:
    """Return [(prime, residues[0..N]), ...], sorted descending by prime."""
    out: list[tuple[int, list[int]]] = []
    seen_primes: set[int] = set()
    for path in files:
        try:
            prime, n_max, residues = read_residue_file(path)
        except (ResidueFormatError, FileNotFoundError) as exc:
            raise ArithmeticError(f"cannot use {path}: {exc}") from exc
        if n_max != expected_n:
            raise ArithmeticError(
                f"{path}: N={n_max}, expected {expected_n} (all residue files "
                "must cover the same N as --n)"
            )
        if prime in seen_primes:
            raise ArithmeticError(f"{path}: duplicate prime {prime}")
        seen_primes.add(prime)
        out.append((prime, residues))
    out.sort(key=lambda t: t[0], reverse=True)
    return out


def verify_against_known(
    residues_by_prime: list[tuple[int, list[int]]], known: list[int], source: str
) -> None:
    """Verify residues[n] == known[n] % prime for every prime, n < len(known)."""
    for prime, residues in residues_by_prime:
        limit = min(len(known), len(residues))
        for n in range(limit):
            want = known[n] % prime
            got = residues[n]
            if got != want:
                raise ArithmeticError(
                    f"CERTIFY FAILED: prime={prime} n={n}: residue file has "
                    f"{got}, but {source} gives {known[n]} % {prime} = {want}"
                )
    total_checked = sum(min(len(known), len(r)) for _, r in residues_by_prime)
    print(
        f"CERTIFY: OK, {len(residues_by_prime)} primes each verified against "
        f"{source} for n=0..{len(known) - 1} ({total_checked} residue checks total)"
    )


def minimal_primary_count(primes_desc: list[int], bound: int) -> int:
    product = 1
    for k, p in enumerate(primes_desc, start=1):
        product *= p
        if product > bound:
            return k
    raise ArithmeticError(
        f"all {len(primes_desc)} supplied primes together only reach "
        f"{product.bit_length()} bits; need > {bound.bit_length()} bits (B_N). "
        "Supply more residue files."
    )


def crt_reconstruct(
    residues_by_prime: list[tuple[int, list[int]]],
) -> tuple[list[int], int]:
    """Incremental (Garner) CRT reconstruction across the given primes."""
    length = len(residues_by_prime[0][1])
    values = [0] * length
    modulus_product = 1
    for prime, sequence in residues_by_prime:
        inverse = pow(modulus_product % prime, -1, prime)
        for n in range(length):
            correction = ((sequence[n] - values[n]) % prime) * inverse % prime
            values[n] += modulus_product * correction
        modulus_product *= prime
    return values, modulus_product


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("residue_files", nargs="*", help="explicit residue files (else use --residues-dir)")
    ap.add_argument("--residues-dir", type=Path, default=None)
    ap.add_argument("--n", type=int, required=True, help="N that every residue file must cover")
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--data-file", type=Path, default=DEFAULT_DATA_FILE)
    ap.add_argument("--skip-hash-check", action="store_true")
    args = ap.parse_args()

    files = find_residue_files(args)
    print(f"found {len(files)} residue file(s)")

    residues_by_prime = load_all(files, args.n)
    if not residues_by_prime:
        raise SystemExit("no usable residue files")

    known = read_known_prefix(
        args.data_file, None if args.skip_hash_check else DEFAULT_DATA_SHA256
    )
    verify_against_known(residues_by_prime, known, str(args.data_file))

    bounds = injection_bounds(args.n)
    bound = bounds[args.n]
    print(f"B_{args.n} has {bound.bit_length()} bits (exact bona_bound.injection_bounds)")

    primes_desc = [p for p, _ in residues_by_prime]
    primary_count = minimal_primary_count(primes_desc, bound)
    primary = residues_by_prime[:primary_count]
    withheld = residues_by_prime[primary_count:]
    print(
        f"selected {primary_count} primary primes (largest-first) out of "
        f"{len(residues_by_prime)} supplied; {len(withheld)} withheld for checking"
    )

    values, product = crt_reconstruct(primary)
    if product <= bound:
        raise ArithmeticError(
            "internal error: primary product does not exceed the bound "
            "despite minimal_primary_count's guarantee"
        )
    for n, (value, per_n_bound) in enumerate(zip(values, bounds)):
        if not (0 <= value <= per_n_bound):
            raise ArithmeticError(
                f"reconstructed a_{n}={value} violates 0 <= a_n <= B_{n}={per_n_bound}"
            )
    print(f"per-n bound check: OK for n=0..{args.n}")

    for prime, sequence in withheld:
        for n in range(len(values)):
            if values[n] % prime != sequence[n]:
                raise ArithmeticError(
                    f"WITHHELD CHECK FAILED: prime={prime} n={n}: reconstructed "
                    f"a_n mod p = {values[n] % prime}, residue file has {sequence[n]}"
                )
    print(f"withheld-prime check: OK for all {len(withheld)} withheld primes")

    overlap = min(len(values), len(known))
    if values[:overlap] != known[:overlap]:
        for n in range(overlap):
            if values[n] != known[n]:
                raise ArithmeticError(
                    f"reconstructed a_{n}={values[n]} disagrees with data file "
                    f"value {known[n]} (exact, not just mod p)"
                )
    print(f"exact-prefix check: OK, reconstructed n=0..{overlap - 1} match {args.data_file} exactly")

    text = "".join(f"{n} {v}\n" for n, v in enumerate(values))
    tmp = args.output.with_name(args.output.name + ".tmp")
    tmp.write_text(text, encoding="ascii")
    os.replace(tmp, args.output)

    summary = (
        f"reconstructed={len(values)} primary={primary_count} "
        f"withheld={len(withheld)} bound_bits={bound.bit_length()} "
        f"product_bits={product.bit_length()}"
    )
    print(summary)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ArithmeticError, ValueError) as exc:
        print(f"RECONSTRUCT FAILED: {exc}", file=sys.stderr)
        raise SystemExit(1)
