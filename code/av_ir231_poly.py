#!/usr/bin/env python3
"""Polynomial-time enumeration of Av(iota_r direct-sum 231), for fixed r.

Here ``iota_r = 12...r`` and the forbidden pattern is

    1,2,...,r, r+2,r+3,r+1.

The algorithm reads a permutation from left to right and records the usual
patience-sorting thresholds b_1 < ... < b_r.  Its finite control is the
r-tuple p=(p_0,...,p_{r-1}) of numbers of unused values below b_1 and
between consecutive thresholds.  Whenever a new increasing subsequence of
length r is completed, its top creates a 231-avoidance obligation.  The
unfinished recursive intervals of all such obligations form a stack L of
positive integers.

The literal states H_p(L) have exponentially many possible stacks.  This
implementation eliminates the stack with sparse transfer kernels.  For
ell>0, K[p,ell][t] counts the ways to process everything before a marked
old stack tail, starting with control p and active head ell, and to expose
that unchanged tail with control t.  All dependencies have total rank one
less, where

    rank(p,ell) = sum(p) + ell,

so the kernels can be filled in increasing rank.  Empty-stack values G[p]
are then filled in increasing sum(p), and

    |Av_n(iota_r direct-sum 231)| = G[(n,0,...,0)].

For every fixed r this uses polynomially many exact-integer operations.  A
coarse bound for the direct sparse implementation is O(N^(3r+2)) time and
O(N^(2r+1)) integer storage.  The r=2 specialization is the O(N^8)-time,
O(N^5)-space protected-tail algorithm for Av(12453).
"""

from __future__ import annotations

import argparse
import math
import time
from collections import defaultdict
from itertools import combinations, permutations
from typing import DefaultDict, Dict, Iterable, Iterator, Mapping, Tuple

Control = Tuple[int, ...]
Row = Dict[Control, int]
KernelKey = Tuple[Control, int]


def weak_compositions(total: int, parts: int) -> Iterator[Control]:
    """Yield all weak compositions of ``total`` into ``parts`` parts."""
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for tail in weak_compositions(total - first, parts - 1):
            yield (first,) + tail


def _add_scaled(
    target: DefaultDict[Control, int],
    row: Mapping[Control, int],
    scale: int = 1,
) -> None:
    """Add ``scale * row`` to a sparse row vector."""
    for state, value in row.items():
        target[state] += scale * value


def pattern_ir231(r: int) -> Tuple[int, ...]:
    """Return the classical pattern iota_r direct-sum 231."""
    if r < 1:
        raise ValueError("r must be positive")
    return tuple(range(1, r + 1)) + (r + 2, r + 3, r + 1)


def count_avoiders(max_n: int, r: int) -> Tuple[list[int], int, int]:
    """Return counts through ``max_n`` and sparse-kernel diagnostics.

    The returned triple is ``(coefficients, kernel_rows, nonzero_entries)``.
    The convenient padded kernel region ``sum(p)+ell <= max_n`` is used;
    the root computation itself only needs rank at most ``max_n-1``.
    """
    if max_n < 0:
        raise ValueError("max_n must be nonnegative")
    if r < 1:
        raise ValueError("r must be positive")

    kernels: Dict[KernelKey, Row] = {}

    # Every term on the right has rank one less.  For a fixed rank, ell and
    # the weak composition p therefore may be visited in any order.
    for rank in range(1, max_n + 1):
        for ell in range(1, rank + 1):
            control_weight = rank - ell
            for p in weak_compositions(control_weight, r):
                row: DefaultDict[Control, int] = defaultdict(int)

                # Read a value from a band below b_r.  This replaces
                # b_{band+1} and transfers the values above it to the next
                # band, without creating a new 231-obligation.
                for band in range(r - 1):
                    old_size = p[band]
                    for h in range(old_size):
                        target = list(p)
                        target[band] = h
                        target[band + 1] += old_size - 1 - h
                        _add_scaled(row, kernels[(tuple(target), ell)])

                # Read a value in the last band.  It becomes the new b_r;
                # the d old values above it fuse into the active stack head.
                old_size = p[-1]
                for h in range(old_size):
                    d = old_size - 1 - h
                    target = p[:-1] + (h,)
                    _add_scaled(row, kernels[(target, ell + d)])

                # Process one value belonging to the active 231 interval.
                # At ell=1 the marked old tail is exposed immediately.
                if ell == 1:
                    row[p] += 1
                else:
                    _add_scaled(row, kernels[(p, ell - 1)], 2)

                # An interior value splits the active 231 interval into two
                # consecutive intervals; compose their transfer rows.
                for a in range(1, ell - 1):
                    b = ell - 1 - a
                    for middle, multiplicity in kernels[(p, a)].items():
                        _add_scaled(
                            row,
                            kernels[(middle, b)],
                            multiplicity,
                        )

                kernels[(p, ell)] = dict(row)

    # Empty-stack values.  Every transition consumes one unused value, so
    # increasing total control weight is a topological order.
    empty: Dict[Control, int] = {(0,) * r: 1}
    for weight in range(1, max_n + 1):
        for p in weak_compositions(weight, r):
            value = 0

            for band in range(r - 1):
                old_size = p[band]
                for h in range(old_size):
                    target = list(p)
                    target[band] = h
                    target[band + 1] += old_size - 1 - h
                    value += empty[tuple(target)]

            old_size = p[-1]
            for h in range(old_size):
                d = old_size - 1 - h
                target = p[:-1] + (h,)
                if d == 0:
                    value += empty[target]
                else:
                    value += sum(
                        multiplicity * empty[endpoint]
                        for endpoint, multiplicity
                        in kernels[(target, d)].items()
                    )

            empty[p] = value

    zero_tail = (0,) * (r - 1)
    coefficients = [empty[(n,) + zero_tail] for n in range(max_n + 1)]
    nonzero_entries = sum(len(row) for row in kernels.values())
    return coefficients, len(kernels), nonzero_entries


def _avoids_pattern(permutation: Tuple[int, ...], pattern: Control) -> bool:
    """Direct pattern test, used only by the optional small-n verifier."""
    length = len(pattern)
    for indices in combinations(range(len(permutation)), length):
        values = tuple(permutation[index] for index in indices)
        reduction = tuple(
            1 + sum(other < value for other in values) for value in values
        )
        if reduction == pattern:
            return False
    return True


def verify_by_brute_force(
    coefficients: list[int], r: int, through_n: int
) -> None:
    """Raise AssertionError unless the requested small terms pass brute force."""
    through_n = min(through_n, len(coefficients) - 1)
    pattern = pattern_ir231(r)
    for n in range(through_n + 1):
        direct = sum(
            _avoids_pattern(permutation, pattern)
            for permutation in permutations(range(1, n + 1))
        )
        if direct != coefficients[n]:
            raise AssertionError(
                f"n={n}: transfer algorithm gave {coefficients[n]}, "
                f"brute force gave {direct}"
            )


def main(argv: Iterable[str] | None = None) -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Compute the counting sequence for "
            "Av(iota_r direct-sum 231), for fixed r."
        )
    )
    parser.add_argument("r", type=int, help="length of the increasing prefix")
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
    coefficients, rows, entries = count_avoiders(args.max_n, args.r)
    elapsed = time.perf_counter() - started
    if args.verify_small >= 0:
        verify_by_brute_force(coefficients, args.r, args.verify_small)

    pattern = ",".join(map(str, pattern_ir231(args.r)))
    print(f"# r={args.r} pattern={pattern}")
    for n, value in enumerate(coefficients):
        print(f"{n} {value}")
    expected_rows = math.comb(args.max_n + args.r, args.r + 1)
    print(
        f"# kernel_rows={rows} expected_rows={expected_rows} "
        f"nonzero_entries={entries} seconds={elapsed:.3f}"
    )
    if args.verify_small >= 0:
        checked = min(args.verify_small, args.max_n)
        print(f"# brute_force_verified_through={checked}")


if __name__ == "__main__":
    main()
