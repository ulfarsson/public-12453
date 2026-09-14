#!/usr/bin/env python3
"""Reconstruct exact Av(12453) coefficients from packed RNS checkpoints.

The first 18 primes are used for CRT reconstruction through n=150.  Exact
coefficients of Av(1342), together with the left-to-right-minimum deletion
injection, certify that their product is large enough.  Every remaining
prime is reserved as an independent congruence check.
"""

from __future__ import annotations

import argparse
import math
import os
from pathlib import Path


def av1342_counts(maximum: int) -> list[int]:
    """Return b_m=|Av_m(1342)| from Bóna's algebraic generating function."""
    if maximum < 0:
        return []
    b = [1]
    if maximum >= 1:
        b.append(1)
    if maximum >= 2:
        b.append(2)
    s = 24  # [x^2](1-8x)^(3/2)
    for n in range(3, maximum + 1):
        numerator = s * 4 * (2 * n - 5)
        if numerator % n:
            raise ArithmeticError("nonexact binomial-series division")
        s = numerator // n
        value = s // 2 - 3 * b[n - 1] - 3 * b[n - 2] - b[n - 3]
        if value < 0:
            raise ArithmeticError("negative Av(1342) coefficient")
        b.append(value)
    return b


def injection_bounds(maximum: int) -> list[int]:
    """Return sum_m binom(n,m)^2 |Av_m(1342)| for every n<=maximum."""
    b = av1342_counts(maximum)
    return [
        sum(math.comb(n, m) ** 2 * b[m] for m in range(n + 1))
        for n in range(maximum + 1)
    ]


def read_residues(paths: list[Path]) -> list[tuple[int, list[int]]]:
    result: list[tuple[int, list[int]]] = []
    for path in paths:
        prime: int | None = None
        coefficients: list[int] = []
        for raw_line in path.read_text(encoding="ascii").splitlines():
            line = raw_line.strip()
            if not line:
                continue
            if line.startswith("# modulus "):
                if prime is not None:
                    result.append((prime, coefficients))
                prime = int(line.removeprefix("# modulus "))
                coefficients = []
                continue
            if prime is None:
                raise ValueError(f"coefficient before modulus in {path}")
            degree_text, residue_text = line.split()
            degree = int(degree_text)
            if degree != len(coefficients):
                raise ValueError(f"nonconsecutive degree in {path}: {degree}")
            coefficients.append(int(residue_text))
        if prime is not None:
            result.append((prime, coefficients))
    if not result:
        raise ValueError("no modular sequences found")
    length = len(result[0][1])
    if any(len(values) != length for _, values in result):
        raise ValueError("residue sequences have different lengths")
    primes = [prime for prime, _ in result]
    if len(set(primes)) != len(primes):
        raise ValueError("duplicate modulus")
    return result


def read_independent_residues(specifications: list[str]) -> list[tuple[int, list[int]]]:
    """Read PRIME:PATH specifications for plain two-column residue files."""
    result: list[tuple[int, list[int]]] = []
    for specification in specifications:
        prime_text, separator, path_text = specification.partition(":")
        if not separator or not prime_text or not path_text:
            raise ValueError(
                "--independent-residue must have the form PRIME:PATH"
            )
        prime = int(prime_text)
        path = Path(path_text)
        coefficients: list[int] = []
        for raw_line in path.read_text(encoding="ascii").splitlines():
            line = raw_line.strip()
            if not line or line.startswith("#"):
                continue
            degree_text, residue_text = line.split()
            degree = int(degree_text)
            if degree != len(coefficients):
                raise ValueError(f"nonconsecutive degree in {path}: {degree}")
            coefficients.append(int(residue_text))
        if not coefficients:
            raise ValueError(f"no residues found in {path}")
        result.append((prime, coefficients))
    return result


def reconstruct(
    residues: list[tuple[int, list[int]]], primary_count: int
) -> tuple[list[int], int]:
    if not 1 <= primary_count <= len(residues):
        raise ValueError("invalid primary-prime count")
    length = len(residues[0][1])
    values = [0] * length
    modulus_product = 1
    for prime, sequence in residues[:primary_count]:
        inverse = pow(modulus_product % prime, -1, prime)
        for n, residue in enumerate(sequence):
            correction = ((residue - values[n]) % prime) * inverse % prime
            values[n] += modulus_product * correction
        modulus_product *= prime
    return values, modulus_product


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("residue_files", nargs="+", type=Path)
    parser.add_argument("--primary-count", type=int, default=18)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--known-prefix", type=Path)
    parser.add_argument(
        "--independent-residue",
        action="append",
        default=[],
        metavar="PRIME:PATH",
        help="separately computed two-column residue sequence (repeatable)",
    )
    args = parser.parse_args()

    residues = read_residues(args.residue_files)
    values, product = reconstruct(residues, args.primary_count)
    bounds = injection_bounds(len(values) - 1)
    if product <= max(bounds):
        raise ArithmeticError("primary CRT product does not exceed exact bound")
    for n, (value, bound) in enumerate(zip(values, bounds)):
        if not 0 <= value <= bound:
            raise ArithmeticError(f"coefficient a_{n} exceeds its exact bound")

    redundant = residues[args.primary_count :]
    for prime, sequence in redundant:
        for n, (value, residue) in enumerate(zip(values, sequence)):
            if value % prime != residue:
                raise ArithmeticError(
                    f"redundant residue failed at n={n}, p={prime}")

    independent = (
        read_independent_residues(args.independent_residue)
        if args.independent_residue
        else []
    )
    for prime, sequence in independent:
        if len(sequence) != len(values):
            raise ValueError(
                f"independent sequence has length {len(sequence)}, "
                f"expected {len(values)}"
            )
        for n, (value, residue) in enumerate(zip(values, sequence)):
            if value % prime != residue:
                raise ArithmeticError(
                    f"independent residue failed at n={n}, p={prime}"
                )

    if args.known_prefix is not None:
        known = []
        for line in args.known_prefix.read_text(encoding="ascii").splitlines():
            if line.strip() and not line.startswith("#"):
                degree_text, value_text = line.split()
                if int(degree_text) != len(known):
                    raise ValueError("known prefix has nonconsecutive degrees")
                known.append(int(value_text))
        overlap = min(len(values), len(known))
        if values[:overlap] != known[:overlap]:
            raise ArithmeticError("reconstructed coefficients disagree with prefix")

    text = "".join(f"{n} {value}\n" for n, value in enumerate(values))
    temporary = args.output.with_name(args.output.name + ".tmp")
    temporary.write_text(text, encoding="ascii")
    os.replace(temporary, args.output)
    print(
        f"reconstructed={len(values)} primary={args.primary_count} "
        f"redundant={len(redundant)} independent={len(independent)} "
        f"bound_bits={max(bounds).bit_length()} "
        f"product_bits={product.bit_length()}"
    )


if __name__ == "__main__":
    main()
