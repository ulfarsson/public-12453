"""Shared residue-file I/O and validation for the Av(12453) n=300 harness.

File format written/read by every tool in this directory ("the engine's own
format" per the task brief):

    # prime <P> <N>
    0 <residue_0>
    1 <residue_1>
    ...
    N <residue_N>

Exactly one header line, then exactly N+1 data lines for n = 0..N in order
(blank lines are tolerated and skipped), each residue an integer in
[0, P).  This module is used by run_all.sh (as a CLI: `python3 residue_io.py
check FILE [PRIME] [N]`), reconstruct.py, and compare_residues.py, so the
format is defined and validated in exactly one place.
"""

from __future__ import annotations

import sys
from pathlib import Path


class ResidueFormatError(ValueError):
    pass


def read_header(path: str | Path) -> tuple[int, int]:
    """Return (P, N) from a residue file's header line only (cheap)."""
    p = Path(path)
    with p.open("r", encoding="ascii") as f:
        for raw in f:
            line = raw.strip()
            if not line:
                continue
            return _parse_header(line, p)
    raise ResidueFormatError(f"{p}: empty file")


def _parse_header(line: str, path: Path) -> tuple[int, int]:
    parts = line.split()
    if len(parts) != 4 or parts[0] != "#" or parts[1] != "prime":
        raise ResidueFormatError(f"{path}: bad header line {line!r}")
    try:
        prime = int(parts[2])
        n = int(parts[3])
    except ValueError as exc:
        raise ResidueFormatError(f"{path}: bad header numbers {line!r}") from exc
    if prime < 2:
        raise ResidueFormatError(f"{path}: header prime {prime} < 2")
    if n < 0:
        raise ResidueFormatError(f"{path}: header N {n} < 0")
    return prime, n


def read_residue_file(path: str | Path) -> tuple[int, int, list[int]]:
    """Parse a full residue file.  Returns (P, N, residues[0..N]).

    Raises ResidueFormatError on any structural problem: bad header, wrong
    number of data lines, out-of-order or duplicate n, a residue outside
    [0, P), or a missing n.  This is a full, exact parse (not the "quick"
    structural check below) -- callers that need every value (reconstruct.py,
    compare_residues.py) should use this.
    """
    p = Path(path)
    try:
        lines = p.read_text(encoding="ascii").splitlines()
    except FileNotFoundError:
        raise
    except UnicodeDecodeError as exc:
        raise ResidueFormatError(f"{p}: not ASCII text ({exc})") from exc

    nonblank = [ln for ln in lines if ln.strip() != ""]
    if not nonblank:
        raise ResidueFormatError(f"{p}: empty file")

    prime, n_max = _parse_header(nonblank[0], p)
    data_lines = [ln for ln in nonblank[1:] if not ln.lstrip().startswith("#")]
    expected = n_max + 1
    if len(data_lines) != expected:
        raise ResidueFormatError(
            f"{p}: expected {expected} data lines (n=0..{n_max}), "
            f"got {len(data_lines)}"
        )

    residues: list[int | None] = [None] * expected
    for ln in data_lines:
        parts = ln.split()
        if len(parts) != 2:
            raise ResidueFormatError(f"{p}: malformed data line {ln!r}")
        try:
            n = int(parts[0])
            r = int(parts[1])
        except ValueError as exc:
            raise ResidueFormatError(f"{p}: non-integer data line {ln!r}") from exc
        if not (0 <= n <= n_max):
            raise ResidueFormatError(f"{p}: n={n} out of range [0,{n_max}]")
        if residues[n] is not None:
            raise ResidueFormatError(f"{p}: duplicate entry for n={n}")
        if not (0 <= r < prime):
            raise ResidueFormatError(
                f"{p}: residue at n={n} is {r}, not in [0,{prime})"
            )
        residues[n] = r

    missing = [n for n, r in enumerate(residues) if r is None]
    if missing:
        raise ResidueFormatError(
            f"{p}: missing n values {missing[:8]}"
            + (" ..." if len(missing) > 8 else "")
        )
    return prime, n_max, residues  # type: ignore[return-value]


def write_residue_file(path: str | Path, prime: int, n_max: int, residues: list[int]) -> None:
    """Write a residue file atomically (write to .tmp then os.replace)."""
    import os

    if len(residues) != n_max + 1:
        raise ValueError(f"len(residues)={len(residues)} != N+1={n_max + 1}")
    p = Path(path)
    tmp = p.with_name(p.name + f".tmp{os.getpid()}")
    with tmp.open("w", encoding="ascii") as f:
        f.write(f"# prime {prime} {n_max}\n")
        for n, r in enumerate(residues):
            if not (0 <= r < prime):
                raise ValueError(f"residue at n={n} is {r}, not in [0,{prime})")
            f.write(f"{n} {r}\n")
    os.replace(tmp, p)


def quick_check(
    path: str | Path, expected_prime: int | None = None, expected_n: int | None = None
) -> tuple[bool, str]:
    """Cheap-but-exact structural validity check; returns (ok, reason).

    Used by run_all.sh to decide whether an existing residues/<p>.txt can be
    skipped.  Does a full parse (residue files at N=300 are only ~301
    lines, so this is not actually expensive) rather than a line-count-only
    heuristic, so a truncated or corrupted-header file is never mistaken for
    a good one.
    """
    try:
        prime, n_max, _residues = read_residue_file(path)
    except FileNotFoundError:
        return False, "missing file"
    except ResidueFormatError as exc:
        return False, str(exc)
    if expected_prime is not None and prime != expected_prime:
        return False, f"prime mismatch: file has {prime}, expected {expected_prime}"
    if expected_n is not None and n_max != expected_n:
        return False, f"N mismatch: file has {n_max}, expected {expected_n}"
    return True, "ok"


def _main(argv: list[str]) -> int:
    if len(argv) < 2 or argv[0] != "check":
        print(
            "usage: residue_io.py check FILE [EXPECTED_PRIME] [EXPECTED_N]",
            file=sys.stderr,
        )
        return 2
    path = argv[1]
    expected_prime = int(argv[2]) if len(argv) > 2 else None
    expected_n = int(argv[3]) if len(argv) > 3 else None
    ok, reason = quick_check(path, expected_prime, expected_n)
    print(("OK " if ok else "FAIL ") + reason)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(_main(sys.argv[1:]))
