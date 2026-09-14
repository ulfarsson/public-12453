"""Exact computation of |Av_m(1342)| and the CRT injection bound B_N.

Independent, from-scratch derivation (no reliance on
repo/code/reconstruct_av12453_rns.py's recurrence): expand Bona's algebraic
identity

    2 (1+x)^3 * sum_m b_m x^m  =  (1-8x)^(3/2) + 1 + 20x - 8x^2

as formal power series with exact rationals (fractions.Fraction), then
divide by 2(1+x)^3 by multiplying by its power-series inverse.  b_m are
verified to come out as non-negative integers.

B_N = sum_{m=0}^{N} C(N,m)^2 * b_m is the exact upper bound (from the
left-to-right-minimum deletion injection into Av(1342) pairs) used to size
the CRT modulus product for reconstructing a_N = |Av_N(12453)|.

Both functions are pure and memoize nothing across calls; callers wanting
b_0..b_M and B_0..B_N should call once with the largest M/N they need and
slice, since each call recomputes from m=0.
"""

from __future__ import annotations

import math
from fractions import Fraction


def av1342_counts(max_m: int) -> list[int]:
    """Return [b_0, b_1, ..., b_max_m], b_m = |Av_m(1342)|, via Bona's GF.

    Method: build the series T(x) = (1-8x)^(3/2) = sum_k term_k x^k using the
    generalized binomial theorem with r = 3/2 and exact Fraction coefficients
    (term_k = C(r,k) * (-8)^k, computed by the standard ratio recurrence
    term_k = term_{k-1} * (r-k+1)/k * (-8)).  Add the polynomial correction
    1 + 20x - 8x^2 to get U(x) = 2(1+x)^3 * B(x).  Multiply U(x) by the exact
    power-series inverse V(x) = 1/(1+x)^3 (computed from the finite
    polynomial (1+x)^3 = 1+3x+3x^2+x^3 by the standard reciprocal
    recurrence).  b_m = (1/2) * [U*V]_m, verified to be an integer.
    """
    if max_m < 0:
        return []
    r = Fraction(3, 2)

    # T(x) = (1-8x)^(3/2): term_k = C(r,k) (-8)^k
    term: list[Fraction] = [Fraction(1)]
    for k in range(1, max_m + 1):
        term.append(term[-1] * (r - (k - 1)) * Fraction(-8) / k)

    # U(x) = T(x) + 1 + 20x - 8x^2  (= 2(1+x)^3 * B(x))
    u = list(term)
    u[0] += 1
    if max_m >= 1:
        u[1] += 20
    if max_m >= 2:
        u[2] += -8

    # V(x) = 1/(1+x)^3, via reciprocal of P(x)=1+3x+3x^2+x^3 (P0=1):
    #   v_0 = 1
    #   v_k = -(3 v_{k-1} + 3 v_{k-2} + v_{k-3})   (missing terms are 0)
    v: list[Fraction] = [Fraction(1)]
    for k in range(1, max_m + 1):
        acc = Fraction(3) * v[k - 1]
        if k >= 2:
            acc += Fraction(3) * v[k - 2]
        if k >= 3:
            acc += v[k - 3]
        v.append(-acc)

    # b_m = (1/2) * sum_{i=0}^m u_i * v_{m-i}
    b: list[int] = []
    for m in range(max_m + 1):
        s = Fraction(0)
        for i in range(m + 1):
            s += u[i] * v[m - i]
        s /= 2
        if s.denominator != 1:
            raise ArithmeticError(
                f"b_{m} is not an integer: {s} (Bona-series expansion bug)"
            )
        value = s.numerator
        if value < 0:
            raise ArithmeticError(f"b_{m} = {value} < 0 (Bona-series expansion bug)")
        b.append(value)
    return b


_KNOWN_B0_8 = [1, 1, 2, 6, 23, 103, 512, 2740, 15485]


def self_check() -> None:
    """Verify b_0..b_8 against the values quoted in the task brief."""
    b = av1342_counts(8)
    if b != _KNOWN_B0_8:
        raise AssertionError(f"b_0..b_8 = {b}, expected {_KNOWN_B0_8}")


def injection_bounds(max_n: int) -> list[int]:
    """Return [B_0, B_1, ..., B_max_n], B_n = sum_m C(n,m)^2 b_m."""
    b = av1342_counts(max_n)
    return [
        sum(math.comb(n, m) ** 2 * b[m] for m in range(n + 1))
        for n in range(max_n + 1)
    ]


def injection_bound(n: int) -> int:
    """Return B_n alone (recomputes b_0..b_n; use injection_bounds for a range)."""
    return injection_bounds(n)[n]


if __name__ == "__main__":
    import sys

    self_check()
    print("self-check OK: b_0..b_8 =", av1342_counts(8))
    for n in (100, 150, 300):
        bn = injection_bound(n)
        print(f"B_{n} has {bn.bit_length()} bits")
    if len(sys.argv) > 1:
        n = int(sys.argv[1])
        bn = injection_bound(n)
        print(f"B_{n} = {bn}")
        print(f"B_{n} bit_length = {bn.bit_length()}")
