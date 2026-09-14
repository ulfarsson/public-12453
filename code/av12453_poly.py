#!/usr/bin/env python3
"""Polynomial-time enumeration of Av(12453), hence its Wilf class.

The recurrence can be derived by using 12453 = 12 direct-sum 231 and
reading a permutation from left to right.  Every completed increasing pair
creates a requirement that a certain future upper subsequence avoid 231.
The unfinished recursive
intervals of these 231-avoidance requirements form a composition-valued
stack L.  This is the recurrence published as the Biers-Ariel program linked
from OEIS A116485.

This program compresses that composition-valued state.  Write H(i,j,L),
where L is either the empty composition or a tuple of positive parts.  The
key quantity below is

    K[i,j,l][u,v],

the number of recursion paths which start with control (i,j) and top stack
part l, process everything before the marked old tail (including material
later fused into the head), and expose that unchanged tail with control
(u,v).

All dependencies have rank one less, where rank = j + (sum of stack parts),
so the kernels can be filled in increasing order of j+l.  If max_n=N, the
implementation stores the convenient padded region j+l <= N+2 (the tight
cutoff is N+1).  The final empty-stack values G(i,j)
are then filled in increasing j, and |Av_n(12453)| = G(n+1,n+2).

The implementation deliberately mirrors the proof recurrence rather than
trying to optimize constants.  It uses polynomially many exact-integer
operations (a coarse bound is O(N^8) arithmetic operations and O(N^5)
integer storage).
"""

from __future__ import annotations

import argparse
import time
from collections import defaultdict
from itertools import combinations, permutations
from typing import DefaultDict, Dict, Iterable, Mapping, Tuple

Control = Tuple[int, int]
Row = Dict[Control, int]
KernelKey = Tuple[int, int, int]


def _add_scaled(target: DefaultDict[Control, int], row: Mapping[Control, int],
                scale: int = 1) -> None:
    """Add ``scale * row`` to a sparse row vector."""
    for state, value in row.items():
        target[state] += scale * value


def count_avoiders(max_n: int) -> Tuple[list[int], int, int]:
    """Return |Av_n(12453)| for 0 <= n <= max_n.

    The two extra returned integers are the number of kernel rows and the
    number of stored nonzero kernel entries.  They are useful for checking
    the polynomial state compression empirically.
    """
    if max_n < 0:
        raise ValueError("max_n must be nonnegative")

    limit = max_n + 2
    kernels: Dict[KernelKey, Row] = {}

    # K_l((i,j),-), in increasing rank j+l.  Every right-hand-side kernel
    # has smaller rank.  Controls always satisfy 1 <= i < j.
    for rank in range(3, limit + 1):
        for j in range(2, rank):
            ell = rank - j
            for i in range(1, j):
                row: DefaultDict[Control, int] = defaultdict(int)

                # H(i,j,L) -> H(k,j-1,L), 1 <= k < i.
                for k in range(1, i):
                    _add_scaled(row, kernels[k, j - 1, ell])

                # H(i,j,lL) -> H(i,k,(l+j-k-1)L), i < k < j.
                for k in range(i + 1, j):
                    delta = j - k - 1
                    _add_scaled(row, kernels[i, k, ell + delta])

                # Decrement the top part.  At ell=1 this exposes the old
                # tail immediately, without changing the control state.
                if ell == 1:
                    row[i, j] += 1
                else:
                    _add_scaled(row, kernels[i, j, ell - 1], 2)

                # Split ell into a,b with a+b=ell-1.  The transfer for a is
                # followed by the transfer for b, i.e. sparse row-by-matrix
                # multiplication.
                for a in range(1, ell - 1):
                    b = ell - 1 - a
                    for middle, multiplicity in kernels[i, j, a].items():
                        _add_scaled(
                            row,
                            kernels[middle[0], middle[1], b],
                            multiplicity,
                        )

                kernels[i, j, ell] = dict(row)

    # Empty-stack values.  The unique terminal state is (1,2).  All other
    # dependencies have strictly smaller second coordinate, so increasing j
    # is a topological order.
    empty: Dict[Control, int] = {}
    for j in range(2, limit + 1):
        for i in range(1, j):
            if (i, j) == (1, 2):
                empty[i, j] = 1
                continue

            value = 0
            for k in range(1, i):
                value += empty[k, j - 1]

            for k in range(i + 1, j):
                delta = j - k - 1
                if delta == 0:
                    value += empty[i, k]
                else:
                    value += sum(
                        multiplicity * empty[end]
                        for end, multiplicity in kernels[i, k, delta].items()
                    )

            empty[i, j] = value

    coefficients = [empty[n + 1, n + 2] for n in range(max_n + 1)]
    nonzero_entries = sum(len(row) for row in kernels.values())
    return coefficients, len(kernels), nonzero_entries


def _avoids_12453(permutation: Tuple[int, ...]) -> bool:
    """Direct pattern test, used only by the optional small-n verifier."""
    pattern = (1, 2, 4, 5, 3)
    for indices in combinations(range(len(permutation)), 5):
        values = tuple(permutation[index] for index in indices)
        reduction = tuple(
            1 + sum(other < value for other in values) for value in values
        )
        if reduction == pattern:
            return False
    return True


def verify_by_brute_force(coefficients: list[int], through_n: int) -> None:
    """Raise AssertionError unless the requested small terms pass brute force."""
    through_n = min(through_n, len(coefficients) - 1)
    for n in range(through_n + 1):
        direct = sum(_avoids_12453(p) for p in permutations(range(1, n + 1)))
        if direct != coefficients[n]:
            raise AssertionError(
                f"n={n}: transfer algorithm gave {coefficients[n]}, "
                f"brute force gave {direct}"
            )


def main(argv: Iterable[str] | None = None) -> None:
    parser = argparse.ArgumentParser(
        description="Compute the Av(12453)=Av(31245) counting sequence."
    )
    parser.add_argument("max_n", nargs="?", type=int, default=20)
    parser.add_argument(
        "--verify-small",
        type=int,
        default=-1,
        metavar="N",
        help="also check terms through N by direct permutation enumeration",
    )
    args = parser.parse_args(argv)

    started = time.perf_counter()
    coefficients, rows, entries = count_avoiders(args.max_n)
    elapsed = time.perf_counter() - started
    if args.verify_small >= 0:
        verify_by_brute_force(coefficients, args.verify_small)
    for n, value in enumerate(coefficients):
        print(f"{n} {value}")
    print(
        f"# kernel_rows={rows} nonzero_entries={entries} "
        f"seconds={elapsed:.3f}"
    )
    if args.verify_small >= 0:
        checked = min(args.verify_small, args.max_n)
        print(f"# brute_force_verified_through={checked}")


if __name__ == "__main__":
    main()
