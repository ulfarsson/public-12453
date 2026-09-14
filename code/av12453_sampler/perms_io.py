#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""perms_io.py -- pure-Python reader for the two sample formats of `sampler`.

The sampler writes permutations of 1..n either as

  text    one permutation per line, values 1..n, space separated
          (``--out FILE``), or
  binary  a flat stream of little-endian uint16 values, n per record, with no
          header and no separators (``--binary FILE``).

The binary form is 2n bytes per sample instead of about 4n, and it needs no
parsing; with numpy it is simply

    a = np.fromfile(FILE, dtype='<u2').reshape(-1, n)     # values 1..n

but this module reads it without numpy (it is used with pypy3, where numpy is
not available).  Both readers yield the same objects -- lists of ints -- so a
consumer can be written once:

    from perms_io import iter_perms
    for pi in iter_perms("s300.bin", n=300):     # or iter_perms("s300.txt")
        ...

Library
-------
    iter_text(path)                 yield [int, ...] per line
    iter_binary(path, n)            yield [int, ...] per record
    iter_perms(path, n=None, binary=None)
                                    auto-detects the format (binary needs n)
    count_records(path, n=None, binary=None)
    looks_binary(path)              format sniffer
    write_text(path, perms)         write the text form
    write_binary(path, perms)       write the binary form
    check_perms(it, n=None)         sanity-check that every record is a
                                    permutation of 1..n; returns (count, n)

CLI
---
    python3 perms_io.py FILE --n 300 --count
    python3 perms_io.py FILE --n 300 --head 3
    python3 perms_io.py FILE.txt --to-binary FILE.bin
    python3 perms_io.py FILE.bin --n 300 --to-text FILE.txt
    python3 perms_io.py A.txt --compare B.bin --n 300      # records must agree
    python3 perms_io.py FILE --n 300 --validate            # permutation check
"""

import os
import sys
from array import array

CHUNK = 1 << 16                      # records per binary read

_TEXT_BYTES = frozenset(b"0123456789 \t\r\n")


def looks_binary(path, probe=4096):
    """True if the first `probe` bytes contain anything but digits/space/newline."""
    with open(path, "rb") as f:
        head = f.read(probe)
    if not head:
        return False
    return not set(head) <= _TEXT_BYTES


# ------------------------------------------------------------------ readers
def iter_text(path):
    """Yield one list of ints per non-empty line."""
    with open(path, "r") as f:
        for line in f:
            if not line.strip():
                continue
            yield [int(t) for t in line.split()]


def iter_binary(path, n):
    """Yield one list of n ints per record of little-endian uint16 values."""
    if n is None or n < 1:
        raise ValueError("iter_binary needs the record length n")
    size = os.path.getsize(path)
    rec = 2 * n
    if size % rec:
        raise ValueError("%s: %d bytes is not a multiple of 2*n = %d"
                         % (path, size, rec))
    swap = sys.byteorder != "little"
    with open(path, "rb") as f:
        while True:
            a = array("H")
            try:
                a.fromfile(f, n * CHUNK)
            except EOFError:
                pass                          # short final read: a holds the rest
            if not len(a):
                return
            if swap:
                a.byteswap()
            for i in range(0, len(a), n):
                yield a[i:i + n].tolist()


def iter_perms(path, n=None, binary=None):
    """Yield the permutations of `path`, auto-detecting text vs binary.

    `binary` forces the format; the binary format needs `n`."""
    if binary is None:
        binary = looks_binary(path)
    if binary:
        return iter_binary(path, n)
    return iter_text(path)


def count_records(path, n=None, binary=None):
    """Number of permutations in the file (O(1) for the binary format)."""
    if binary is None:
        binary = looks_binary(path)
    if binary:
        if n is None or n < 1:
            raise ValueError("counting binary records needs n")
        size = os.path.getsize(path)
        if size % (2 * n):
            raise ValueError("%s: %d bytes is not a multiple of 2*n" % (path, size))
        return size // (2 * n)
    k = 0
    with open(path, "r") as f:
        for line in f:
            if line.strip():
                k += 1
    return k


# ------------------------------------------------------------------ writers
def write_text(path, perms):
    """Write an iterable of permutations in the text format."""
    k = 0
    with open(path, "w") as f:
        for pi in perms:
            f.write(" ".join(str(v) for v in pi))
            f.write("\n")
            k += 1
    return k


def write_binary(path, perms):
    """Write an iterable of permutations in the little-endian uint16 format."""
    k = 0
    swap = sys.byteorder != "little"
    with open(path, "wb") as f:
        buf = array("H")
        for pi in perms:
            buf.extend(pi)
            k += 1
            if len(buf) >= 1 << 16:
                if swap:
                    buf.byteswap()
                buf.tofile(f)
                buf = array("H")
        if len(buf):
            if swap:
                buf.byteswap()
            buf.tofile(f)
    return k


# ---------------------------------------------------------------- validation
def check_perms(it, n=None):
    """Consume `it` and check that every record is a permutation of 1..n.

    Returns (count, n).  Raises ValueError on the first offender."""
    k = 0
    for pi in it:
        if n is None:
            n = len(pi)
        if len(pi) != n:
            raise ValueError("record %d has length %d, expected %d" % (k, len(pi), n))
        if sorted(pi) != list(range(1, n + 1)):
            raise ValueError("record %d is not a permutation of 1..%d" % (k, n))
        k += 1
    return k, n


# --------------------------------------------------------------------- CLI
def main(argv):
    import argparse
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("file")
    ap.add_argument("--n", type=int, default=None,
                    help="record length (required for the binary format)")
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--binary", action="store_true", help="force the binary format")
    g.add_argument("--text", action="store_true", help="force the text format")
    ap.add_argument("--count", action="store_true", help="print the number of records")
    ap.add_argument("--head", type=int, default=0, help="print the first K records")
    ap.add_argument("--validate", action="store_true",
                    help="check that every record is a permutation of 1..n")
    ap.add_argument("--to-text", metavar="OUT", default=None)
    ap.add_argument("--to-binary", metavar="OUT", default=None)
    ap.add_argument("--compare", metavar="OTHER", default=None,
                    help="compare the records with those of another file "
                         "(either format); exit 1 on any difference")
    a = ap.parse_args(argv)

    binary = True if a.binary else (False if a.text else None)
    if binary is None:
        binary = looks_binary(a.file)
    if binary and a.n is None:
        ap.error("the binary format needs --n")

    if a.count:
        print(count_records(a.file, a.n, binary))
    if a.head:
        for i, pi in enumerate(iter_perms(a.file, a.n, binary)):
            if i >= a.head:
                break
            print(" ".join(str(v) for v in pi))
    if a.to_text:
        k = write_text(a.to_text, iter_perms(a.file, a.n, binary))
        sys.stderr.write("wrote %s (%d records)\n" % (a.to_text, k))
    if a.to_binary:
        k = write_binary(a.to_binary, iter_perms(a.file, a.n, binary))
        sys.stderr.write("wrote %s (%d records)\n" % (a.to_binary, k))
    if a.validate:
        k, n = check_perms(iter_perms(a.file, a.n, binary), a.n)
        print("%d records, all permutations of 1..%d" % (k, n))
    if a.compare:
        ob = looks_binary(a.compare)
        if ob and a.n is None:
            ap.error("comparing with a binary file needs --n")
        it1 = iter_perms(a.file, a.n, binary)
        it2 = iter_perms(a.compare, a.n, ob)
        k, bad = 0, 0
        first = None
        while True:
            x = next(it1, None)
            y = next(it2, None)
            if x is None and y is None:
                break
            if x is None or y is None:
                print("FAIL: different number of records (after %d)" % k)
                return 1
            if x != y:
                bad += 1
                if first is None:
                    first = k
            k += 1
        print("compared %d records of %s and %s: %d differ%s"
              % (k, a.file, a.compare, bad,
                 "" if bad == 0 else " (first at record %d)" % first))
        print("verdict %s" % ("PASS (identical)" if bad == 0 else "FAIL"))
        return 0 if bad == 0 else 1
    if not (a.count or a.head or a.to_text or a.to_binary or a.validate or a.compare):
        k = count_records(a.file, a.n, binary)
        print("%s: %s format, %d records%s"
              % (a.file, "binary" if binary else "text", k,
                 ", n = %d" % a.n if a.n else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
