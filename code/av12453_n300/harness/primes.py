#!/usr/bin/env python3
"""Prime selection for the Av(12453) n=300 CRT reconstruction.

1. Computes b_m = |Av_m(1342)| from Bona's series and B_N = sum_m C(N,m)^2 b_m
   (bona_bound.py; own exact derivation, verified against the brief's
   quoted b_0..b_8 and against B_150 = 558 bits).
2. Sieves the primes below 2^16 (u16-storage build) and below 2^21
   (u32-storage build; the brief's design (a) uses primes p < 2^21 stored as
   u32, design (b) uses p < 2^16 stored as u16 -- file names below follow
   that storage-width convention, not the primes' own bit length).
3. For N=300, finds the minimum count of each size whose product exceeds
   B_300 (greedy from the largest available prime down: for a target
   "count of factors needed to exceed a bound", taking the k largest
   candidates maximizes the product achievable with k factors, so greedy-
   descending is optimal for minimizing count).
4. Writes primes_u16.txt / primes_u32.txt: the minimal set plus
   WITHHELD_EXTRA more (next-largest, unused) primes for independent
   redundant-prime checks, one prime per line, largest first.

Usage: pypy3 primes.py [--n 300] [--withheld 6] [--outdir .]
"""

from __future__ import annotations

import argparse
from pathlib import Path

from bona_bound import av1342_counts, injection_bound, injection_bounds, self_check

U16_LIMIT = 1 << 16
U32_BUILD_LIMIT = 1 << 21  # design (a): p < 2^21, stored as u32


def sieve_primes_below(limit: int) -> list[int]:
    """Simple sieve of Eratosthenes; primes strictly below `limit`, ascending."""
    if limit <= 2:
        return []
    is_composite = bytearray(limit)  # index i => i is known composite
    is_composite[0] = is_composite[1] = 1
    i = 2
    while i * i < limit:
        if not is_composite[i]:
            span = len(range(i * i, limit, i))
            is_composite[i * i :: i] = b"\x01" * span
        i += 1
    return [i for i in range(2, limit) if not is_composite[i]]


def is_prime_miller_rabin(n: int) -> bool:
    """Deterministic Miller-Rabin, exact for all n < 3.3e24 (n here < 2^21).

    Independent cross-check for the sieve above, using the fixed witness set
    {2,3,5,7,11,13,17,19,23,29,31,37} known to be deterministic for all
    n < 3,317,044,064,679,887,385,961,981 (Pomerance/Sinclair et al.).
    """
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def cross_check_sieve(primes: list[int], limit: int, window: int = 4000) -> None:
    """Independent Miller-Rabin cross-check of the Eratosthenes sieve.

    (a) Every element of `primes` must itself be prime (catches false
        positives, e.g. the bytearray(n)-is-all-zero bug this script had
        during development, which let 65535 and 2097151 through as
        "primes").
    (b) Every integer in the top `window` below `limit` must agree, in
        primality, with membership in `primes` (catches false negatives).
        This window is far larger than the largest prime gap below 2^21
        (< 300), so it fully validates every prime this script can select.
    """
    prime_set = set(primes)
    for p in primes:
        if not is_prime_miller_rabin(p):
            raise AssertionError(f"sieve bug: {p} is in the prime list but is composite")
    lo = max(2, limit - window)
    for n in range(lo, limit):
        in_list = n in prime_set
        actually_prime = is_prime_miller_rabin(n)
        if in_list != actually_prime:
            raise AssertionError(
                f"sieve bug at n={n}: in_list={in_list} but Miller-Rabin says "
                f"prime={actually_prime}"
            )


def minimal_count_exceeding(sorted_desc: list[int], bound: int) -> int:
    """Fewest leading primes (largest-first) whose product exceeds `bound`."""
    product = 1
    for k, p in enumerate(sorted_desc, start=1):
        product *= p
        if product > bound:
            return k
    raise ArithmeticError(
        f"even all {len(sorted_desc)} available primes only reach "
        f"{product.bit_length()} bits, need > {bound.bit_length()}"
    )


def build_set(
    label: str,
    primes_desc: list[int],
    bound: int,
    withheld: int,
) -> tuple[list[int], int]:
    """Return (recommended_list_desc, primary_count)."""
    primary = minimal_count_exceeding(primes_desc, bound)
    total = primary + withheld
    if total > len(primes_desc):
        raise ArithmeticError(
            f"{label}: need {primary} primary + {withheld} withheld = {total} "
            f"primes but only {len(primes_desc)} are available below the limit"
        )
    chosen = primes_desc[:total]
    product = 1
    for p in chosen[:primary]:
        product *= p
    print(
        f"[{label}] {len(primes_desc)} primes available; "
        f"minimum primary count to exceed bound: {primary} "
        f"(product has {product.bit_length()} bits, bound has {bound.bit_length()} bits); "
        f"recommended set: {primary} primary + {withheld} withheld = {total} primes "
        f"(largest={chosen[0]}, smallest kept={chosen[-1]})"
    )
    return chosen, primary


def write_list(path: Path, primes_desc: list[int]) -> None:
    text = "".join(f"{p}\n" for p in primes_desc)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(text, encoding="ascii")
    tmp.replace(path)
    print(f"wrote {path} ({len(primes_desc)} primes, largest first)")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--n", type=int, default=300, help="target N (default 300)")
    ap.add_argument(
        "--withheld", type=int, default=6, help="withheld check primes per set (default 6)"
    )
    ap.add_argument("--outdir", type=Path, default=Path("."))
    args = ap.parse_args()

    self_check()
    b = av1342_counts(8)
    print(f"self-check: b_0..b_8 = {b}")
    assert b == [1, 1, 2, 6, 23, 103, 512, 2740, 15485]

    bounds = injection_bounds(args.n)
    b150 = injection_bound(150) if args.n >= 150 else None
    if b150 is not None:
        print(f"B_150 = {b150.bit_length()} bits (expect 558)")
        assert b150.bit_length() == 558, "B_150 bit length check failed"
    bN = bounds[args.n]
    print(f"B_{args.n} has {bN.bit_length()} bits")

    primes16 = sieve_primes_below(U16_LIMIT)
    primes21 = sieve_primes_below(U32_BUILD_LIMIT)
    print(
        f"sieved {len(primes16)} primes below 2^16, "
        f"{len(primes21)} primes below 2^21"
    )

    primes16_desc = sorted(primes16, reverse=True)
    primes21_desc = sorted(primes21, reverse=True)

    cross_check_sieve(primes16, U16_LIMIT)
    cross_check_sieve(primes21, U32_BUILD_LIMIT)
    print("Miller-Rabin cross-check of both sieves: OK")

    print(f"largest prime below 2^16: {primes16_desc[0]}")
    print(f"largest prime below 2^21: {primes21_desc[0]}")

    set16, primary16 = build_set("u16 (p<2^16)", primes16_desc, bN, args.withheld)
    set21, primary21 = build_set("u32 (p<2^21)", primes21_desc, bN, args.withheld)

    args.outdir.mkdir(parents=True, exist_ok=True)
    write_list(args.outdir / "primes_u16.txt", set16)
    write_list(args.outdir / "primes_u32.txt", set21)

    print(
        f"SUMMARY N={args.n} bound_bits={bN.bit_length()} "
        f"u16_primary={primary16} u16_withheld={args.withheld} u16_total={len(set16)} "
        f"u32_primary={primary21} u32_withheld={args.withheld} u32_total={len(set21)}"
    )


if __name__ == "__main__":
    main()
