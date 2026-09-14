#!/usr/bin/env python3
"""Reduced transfer-kernel enumeration of ``Av(12453)``.

This is the first-coordinate Toeplitz reduction of the ``d=2`` transfer
algorithm in ``av12453_poly.py``.  In normalized coordinates, write

    K_ell((p, q), (c, d))

for the number of paths which process an active ``231`` block of size
``ell`` and expose the protected tail at control ``(c, d)``.  The first
control coordinate never increases.  Consequently, a path ending with first
coordinate ``c`` never visits a smaller first coordinate, and subtracting
``c`` from that coordinate throughout the path is a bijection.  Thus

    K_ell((p, q), (c, d)) = R_ell(p-c, q, d),
    R_ell(a, q, d) := K_ell((a, q), (0, d)).

Only ``R`` is stored below.  This lowers the number of stored integers through
size ``N`` from ``O(N^5)`` to ``O(N^4)``.  A direct evaluation of the reduced
split convolution takes ``O(N^7)`` arithmetic operations; the empty-stack
table is lower order.  As in the unreduced algorithm, all arithmetic is exact.

The returned coefficients are

    |Av_n(12453)| = g(n, 0),

where ``g(p, q)`` is the number of completions from an empty protected stack.
"""

from __future__ import annotations

import argparse
import time
from collections import defaultdict
from typing import DefaultDict, Dict, Mapping, Tuple


# A reduced kernel row is indexed only by the second endpoint coordinate d.
Row = Dict[int, int]
KernelKey = Tuple[int, int, int]  # (ell, first-coordinate drop a, source q)


def _add_scaled(
    target: DefaultDict[int, int], source: Mapping[int, int], scale: int = 1
) -> None:
    """Add ``scale * source`` to a sparse reduced kernel row."""
    for endpoint_d, value in source.items():
        target[endpoint_d] += scale * value


def count_avoiders(max_n: int) -> Tuple[list[int], int, int]:
    """Return coefficients and reduced-kernel diagnostics through ``max_n``.

    The result is ``(coefficients, kernel_rows, nonzero_entries)``.  Kernel
    rows are the triples ``(ell, a, q)`` with ``ell >= 1`` and
    ``ell + a + q <= max_n``.  A row stores the nonzero values
    ``R_ell(a, q, d)``.
    """
    if max_n < 0:
        raise ValueError("max_n must be nonnegative")

    reduced: Dict[KernelKey, Row] = {}

    # The source weight ell+a+q drops by one in every direct term.  In a
    # split, both factors also have smaller source weight, so increasing
    # ``weight`` is a topological order.
    for weight in range(1, max_n + 1):
        for ell in range(1, weight + 1):
            remaining = weight - ell
            for a in range(remaining + 1):
                q = remaining - a
                row: DefaultDict[int, int] = defaultdict(int)

                # Read a value below the current minimum.  If h lower values
                # remain, the other a-h-1 values join the second base band.
                for h in range(a):
                    _add_scaled(row, reduced[ell, h, a + q - h - 1])

                # Read a value from the second base band.  The q-r-1 newly
                # exposed values merge into the active block.
                for r in range(q):
                    delta = q - r - 1
                    _add_scaled(row, reduced[ell + delta, a, r])

                # Consume an endpoint of the active 231 block.  For ell=1,
                # the old tail is exposed at the unchanged full control.
                # That endpoint has first coordinate zero in the reduced row
                # only when a=0.
                if ell == 1:
                    if a == 0:
                        row[q] += 1
                else:
                    _add_scaled(row, reduced[ell - 1, a, q], 2)

                # An interior pivot splits ell into left and right blocks.
                # If the intermediate full control has first coordinate c,
                # the first reduced kernel drops a-c and the second drops c.
                # Summing over c is ordinary convolution in the drop a;
                # endpoint e is the one remaining matched interface.
                for left_ell in range(1, ell - 1):
                    right_ell = ell - 1 - left_ell
                    for left_drop in range(a + 1):
                        right_drop = a - left_drop
                        for middle_q, multiplicity in reduced[
                            left_ell, left_drop, q
                        ].items():
                            _add_scaled(
                                row,
                                reduced[right_ell, right_drop, middle_q],
                                multiplicity,
                            )

                output = {endpoint: value for endpoint, value in row.items() if value}

                # Exact support inherited from the full transfer kernel.
                # For a=0 the diagonal endpoint d=q is possible; otherwise
                # every path has consumed a base value and d <= a+q-1.
                endpoint_bound = q if a == 0 else a + q - 1
                assert all(0 <= endpoint <= endpoint_bound for endpoint in output)
                reduced[ell, a, q] = output

    # Empty-stack values.  All right-hand-side controls have smaller mass.
    empty: Dict[Tuple[int, int], int] = {(0, 0): 1}
    for mass in range(1, max_n + 1):
        for p in range(mass + 1):
            q = mass - p

            value = sum(empty[h, mass - h - 1] for h in range(p))

            for r in range(q):
                ell = q - r - 1
                if ell == 0:
                    # R_0 is the identity kernel.
                    value += empty[p, r]
                    continue

                # K_ell((p,r),(c,d)) = R_ell(p-c,r,d).
                for c in range(p + 1):
                    for d, multiplicity in reduced[ell, p - c, r].items():
                        value += multiplicity * empty[c, d]

            empty[p, q] = value

    coefficients = [empty[n, 0] for n in range(max_n + 1)]
    nonzero_entries = sum(len(row) for row in reduced.values())
    return coefficients, len(reduced), nonzero_entries


def verify_against_full(through_n: int = 15) -> None:
    """Check the reduced table against the independent full-kernel code."""
    if through_n < 0:
        raise ValueError("through_n must be nonnegative")

    from av12453_poly import count_avoiders as count_with_full_kernels

    reduced_coefficients = count_avoiders(through_n)[0]
    full_coefficients = count_with_full_kernels(through_n)[0]
    if reduced_coefficients != full_coefficients:
        raise AssertionError(
            "reduced and full transfer kernels disagree: "
            f"{reduced_coefficients} != {full_coefficients}"
        )


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Count Av(12453) with first-coordinate-reduced kernels."
    )
    parser.add_argument("max_n", nargs="?", type=int, default=15)
    parser.add_argument(
        "--verify",
        action="store_true",
        help="compare all requested coefficients with av12453_poly.py",
    )
    args = parser.parse_args()

    started = time.perf_counter()
    coefficients, rows, entries = count_avoiders(args.max_n)
    elapsed = time.perf_counter() - started

    for n, value in enumerate(coefficients):
        print(n, value)
    print(
        f"# reduced_kernel_rows={rows} nonzero_entries={entries} "
        f"seconds={elapsed:.6f}"
    )

    if args.verify:
        verify_against_full(args.max_n)
        print(f"# verified_against_full_through={args.max_n}")


if __name__ == "__main__":
    main()
