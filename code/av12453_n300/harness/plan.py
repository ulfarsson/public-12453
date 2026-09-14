#!/usr/bin/env python3
"""Total-wall-time planner for the n=300 prime sweep, plus a benchmark table.

run_all.sh runs one prime at a time (each prime's engine run may itself use
multiple threads internally via OpenMP), so the wall time to sweep a whole
prime list is simply (per-prime wall time at that thread count) * (number of
primes) -- threads do not shorten the sweep by running primes concurrently,
only by speeding up each individual prime's run.

Two ways to get the per-prime time for a scenario:
  --scenario 'LABEL:SECONDS:NUM_PRIMES:THREADS'  (repeatable), or
  --per-prime-seconds/--primes/--threads for a single ad-hoc scenario
    (--primes defaults to the line count of primes_u16.txt / primes_u32.txt
    in --primes-dir if present, else must be given).

Also prints the mandatory benchmark table (wall time at N=100,150,200,300,
single-thread and all-threads, peak RSS, multiply-adds) -- filled from
--bench-csv if given (columns: N,threads,wall_s,peak_rss_mib,madds), else
left as TBD placeholders, since at harness-build time the GEMM engine has
not been benchmarked yet.

Usage:
  pypy3 plan.py --per-prime-seconds 130 --primes 61 --threads 8
  pypy3 plan.py --scenario 'u16:410:77:8' --scenario 'u32:130:61:8'
  pypy3 plan.py --scenario 'u16:410:77:8' --bench-csv bench.csv
"""

from __future__ import annotations

import argparse
from pathlib import Path


def human_duration(seconds: float) -> str:
    m, s = divmod(seconds, 60)
    h, m = divmod(m, 60)
    d, h = divmod(h, 24)
    parts = []
    if d:
        parts.append(f"{int(d)}d")
    if h or d:
        parts.append(f"{int(h)}h")
    if m or h or d:
        parts.append(f"{int(m)}m")
    parts.append(f"{s:.1f}s")
    return " ".join(parts)


def count_lines(path: Path) -> int | None:
    if not path.exists():
        return None
    return sum(1 for line in path.read_text().splitlines() if line.strip())


BENCH_NS = [100, 150, 200, 300]
BENCH_COLUMNS = ["N", "threads=1 wall_s", "threads=ALL wall_s", "peak_RSS_MiB", "madds"]


def load_bench_csv(path: Path) -> dict[tuple[int, int], dict[str, str]]:
    """rows keyed by (N, threads) -> {'wall_s':..,'peak_rss_mib':..,'madds':..}"""
    rows: dict[tuple[int, int], dict[str, str]] = {}
    header = None
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        fields = [f.strip() for f in line.split(",")]
        if header is None:
            header = fields
            continue
        row = dict(zip(header, fields))
        key = (int(row["N"]), int(row["threads"]))
        rows[key] = row
    return rows


def print_bench_table(bench: dict[tuple[int, int], dict[str, str]], all_threads: int) -> None:
    print()
    print("Benchmark table (wall time, peak RSS, exact multiply-add count):")
    header = f"{'N':>5} | {'1 thread wall_s':>16} | {f'{all_threads} threads wall_s':>18} | {'peak RSS (MiB)':>14} | {'multiply-adds':>16}"
    print(header)
    print("-" * len(header))
    for n in BENCH_NS:
        r1 = bench.get((n, 1))
        rk = bench.get((n, all_threads))
        w1 = r1["wall_s"] if r1 else "TBD"
        wk = rk["wall_s"] if rk else "TBD"
        rss = (rk or r1 or {}).get("peak_rss_mib", "TBD")
        madds = (rk or r1 or {}).get("madds", "TBD")
        tag = "" if (r1 or rk) else "  (not yet run)"
        print(f"{n:>5} | {w1:>16} | {wk:>18} | {rss:>14} | {madds:>16}{tag}")
    print()
    print(
        "N=300 row is the target computation; extrapolate from N=100/150/200 "
        "once measured (the design doc estimates ~N^6/24 * 1.6 multiply-adds "
        "at GEMM speed, i.e. roughly (300/200)^6 =~ 11.4x the N=200 time)."
    )


def parse_scenario(spec: str) -> tuple[str, float, int, int]:
    parts = spec.split(":")
    if len(parts) != 4:
        raise ValueError(f"--scenario must be LABEL:SECONDS:NUM_PRIMES:THREADS, got {spec!r}")
    label, secs, primes, threads = parts
    return label, float(secs), int(primes), int(threads)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--scenario", action="append", default=[], metavar="LABEL:SECONDS:NUM_PRIMES:THREADS")
    ap.add_argument("--per-prime-seconds", type=float, default=None)
    ap.add_argument("--primes", type=int, default=None)
    ap.add_argument("--threads", type=int, default=None)
    ap.add_argument("--label", default="adhoc")
    ap.add_argument("--primes-dir", type=Path, default=Path("."), help="dir to look for primes_u16.txt/primes_u32.txt for a default --primes count")
    ap.add_argument("--bench-csv", type=Path, default=None)
    ap.add_argument("--all-threads", type=int, default=8, help="thread count for the 'all threads' benchmark column (default 8, the stated quota)")
    args = ap.parse_args()

    scenarios: list[tuple[str, float, int, int]] = [parse_scenario(s) for s in args.scenario]

    if args.per_prime_seconds is not None:
        primes = args.primes
        if primes is None:
            for fname in ("primes_u16.txt", "primes_u32.txt"):
                n = count_lines(args.primes_dir / fname)
                if n is not None:
                    print(f"(--primes not given; using {n} from {args.primes_dir / fname})")
                    primes = n
                    break
        if primes is None or args.threads is None:
            raise SystemExit(
                "--per-prime-seconds requires --primes (or a primes_u*.txt file "
                "in --primes-dir) and --threads"
            )
        scenarios.append((args.label, args.per_prime_seconds, primes, args.threads))

    if scenarios:
        print("Total-time projections (sequential over primes; threads parallelize within one prime):")
        for label, secs, primes, threads in scenarios:
            total = secs * primes
            print(
                f"  [{label}] {secs:g} s/prime x {primes} primes @ {threads} threads "
                f"= {total:.1f} s = {human_duration(total)}"
            )
    else:
        print("(no --scenario or --per-prime-seconds/--primes/--threads given; skipping total-time projection)")

    bench = load_bench_csv(args.bench_csv) if args.bench_csv else {}
    if args.bench_csv and not args.bench_csv.exists():
        print(f"(--bench-csv {args.bench_csv} does not exist yet; showing placeholders)")
        bench = {}
    print_bench_table(bench, args.all_threads)


if __name__ == "__main__":
    main()
