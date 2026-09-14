#!/usr/bin/env python3
"""Reproduce the frozen n=70..100 asymptotic holdout test for Av(12453)."""

from __future__ import annotations

import argparse
import math
from pathlib import Path


def read_terms(path: Path) -> list[int]:
    terms: list[int] = []
    for raw_line in path.read_text(encoding="ascii").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        index_text, value_text = line.split()
        index = int(index_text)
        if index != len(terms):
            raise ValueError(f"expected index {len(terms)}, found {index}")
        terms.append(int(value_text))
    return terms


def least_squares_three(
    columns: list[list[float]], response: list[float]
) -> tuple[float, float, float]:
    """Solve a three-column least-squares problem by modified Gram--Schmidt."""

    orthonormal: list[list[float]] = []
    upper = [[0.0] * 3 for _ in range(3)]
    for column_index, original in enumerate(columns):
        work = original.copy()
        for previous, basis in enumerate(orthonormal):
            coefficient = math.fsum(
                left * right for left, right in zip(basis, work)
            )
            upper[previous][column_index] = coefficient
            work = [
                value - coefficient * basis_value
                for value, basis_value in zip(work, basis)
            ]
        norm = math.sqrt(math.fsum(value * value for value in work))
        if norm == 0.0:
            raise ValueError("rank-deficient least-squares design")
        upper[column_index][column_index] = norm
        orthonormal.append([value / norm for value in work])

    transformed = [
        math.fsum(left * right for left, right in zip(basis, response))
        for basis in orthonormal
    ]
    solution = [0.0] * 3
    for row in range(2, -1, -1):
        remainder = math.fsum(
            upper[row][column] * solution[column]
            for column in range(row + 1, 3)
        )
        solution[row] = (transformed[row] - remainder) / upper[row][row]
    return solution[0], solution[1], solution[2]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("terms", type=Path)
    args = parser.parse_args()
    terms = read_terms(args.terms)
    if len(terms) < 151:
        raise ValueError("terms through a_150 are required")

    mu = 9.0 + 4.0 * math.sqrt(2.0)
    gamma = -17.0 / 4.0
    training = [float(n) for n in range(70, 101)]
    response = [
        math.log(terms[int(n)])
        - n * math.log(mu)
        - gamma * math.log(n)
        for n in training
    ]
    design_columns = [
        [-n ** (1.0 / 3.0) for n in training],
        [1.0 for _ in training],
        [n ** (-1.0 / 3.0) for n in training],
    ]
    kappa, log_c, correction = least_squares_three(
        design_columns, response
    )

    errors: list[float] = []
    for n in range(101, 151):
        predicted_log = (
            n * math.log(mu)
            - kappa * n ** (1.0 / 3.0)
            + gamma * math.log(n)
            + log_c
            + correction * n ** (-1.0 / 3.0)
        )
        errors.append(predicted_log - math.log(terms[n]))

    rms = math.sqrt(sum(error * error for error in errors) / len(errors))
    print(f"mu={mu:.12f} gamma={gamma:.12f}")
    print(
        f"kappa={kappa:.12f} C={math.exp(log_c):.12f} "
        f"h={correction:.12f}"
    )
    print(
        f"holdout=101..150 rms_log_error={rms:.10e} "
        f"max_abs_log_error={max(map(abs, errors)):.10e} "
        f"error_at_150={errors[-1]:.10e}"
    )


if __name__ == "__main__":
    main()
