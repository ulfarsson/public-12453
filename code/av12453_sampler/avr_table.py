#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""avr_table.py -- reader for the AVR1/AVR2 double-precision tables of Av(12453).

File format "AVR1" (little-endian doubles, as written by tables.cpp):

    int32  magic = 0x41565231
    int32  N
    G      doubles for p = 0..N, q = 0..N-p                  (nested that order)
    R      doubles for l = 1..N, a = 0..N-l, q = 0..N-l-a,
                       s = 0..slen(a,q)-1                    (nested that order)

File format "AVR2" (power-of-two scaled), same layout after a 12-byte header:

    int32  magic = 0x41565232
    int32  N
    int32  scale        (exponent per grade unit; 2 in every table so far)
    G, R   doubles, holding

        R'_{l,a}(q,s) = 2^{-scale*(l+a+q)} R_{l,a}(q,s)
        G'_{(p,q)}    = 2^{-scale*(p+q)}   G_{(p,q)}

    The counts reach about 2^{3.8w} at grade w, so the unscaled table
    overflows binary64 beyond N ~ 260 while the scaled entries stay in
    [2^{-2w}, 2^{1.8w}].  Scaling by a power of two is exact, so an AVR2
    table multiplied back by 2^{scale*grade} is bit-identical to the AVR1
    table of the same N.

    G() and R() return the value AS STORED (scaled, for an AVR2 file);
    G_true()/R_true() return the unscaled value as a float when it is
    representable and as an exact Python int otherwise, and
    G_exact()/R_exact() return it as a Fraction.  g_ratio() forms a ratio of
    two G entries with the scale factors applied, which is what the sampler
    tests need.

with the support length

    slen(a,q) = q+1   if a == 0        (support of R_{l,0}(q,.) is {0..q})
              = a+q   if a >= 1        (support of R_{l,a}(q,.) is {0..a+q-1}).

Meaning (paper Sections 5 and 7):
    R(l,a,q,s) = R_{l,a}(q,s) = K_l((a,q),(0,s)), the protected-tail transfer
                 kernel in reduced (first-coordinate-translated) variables;
                 K_l((p,q),(c,t)) = R(l, p-c, q, t) for 0 <= c <= p, else 0.
    G(p,q)     = G_{(p,q)} = H_{(p,q)}(empty), the number of completions from
                 control (p,q) with empty stack;  |Av_n(12453)| = G(n,0).
Entries outside the stated support are not stored and read as 0.0.

Library use:

    from avr_table import AvrTable
    T = AvrTable("N150.avr")
    T.N, T.G(150, 0), T.R(3, 1, 2, 0)
    T.r_index(3, 1, 2, 0)          # index of the double inside the R block
    T.r_row(3, 1, 2)               # the whole row as a memoryview-like slice

CLI:

    python3 avr_table.py FILE --info
    python3 avr_table.py FILE --G 150,0 --G 3,4
    python3 avr_table.py FILE --R 5,2,3,1 --R 1,0,0,0
    python3 avr_table.py FILE --terms 0:150          # G(n,0) for n in range
    python3 avr_table.py FILE --row 5,2,3            # a whole R row
    python3 avr_table.py FILE --dump-r OUT [--max-grade W] [--eps 0]
                                                    # "l a q s value" text dump
"""

import sys
import os
import math
import struct
from array import array
from fractions import Fraction

MAGIC = 0x41565231          # AVR1, unscaled
MAGIC2 = 0x41565232         # AVR2, 2^{-scale*grade} scaled


def slen(a, q):
    """Number of stored terminal coordinates s of the row R_{l,a}(q,.)."""
    return q + 1 if a == 0 else a + q


def _pref(a, q):
    """sum_{q'=0}^{q-1} slen(a,q'):  offset of row q inside the (l,a) block."""
    if a == 0:
        return q * (q + 1) // 2
    return a * q + q * (q - 1) // 2


class AvrTable(object):
    """Random access to the G and R tables of an AVR1 file."""

    def __init__(self, path, use_mmap=False):
        """use_mmap=True keeps the doubles in a shared read-only mapping
        (slower per access, but many worker processes then share one copy)."""
        self.path = path
        self.mmap = bool(use_mmap)
        if self.mmap:
            self._init_mmap(path)
            return
        with open(path, "rb") as f:
            head = f.read(8)
            if len(head) != 8:
                raise ValueError("%s: too short" % path)
            magic, N = struct.unpack("<ii", head)
            if magic not in (MAGIC, MAGIC2):
                raise ValueError("%s: bad magic 0x%08x (expected 0x%08x or 0x%08x)"
                                 % (path, magic & 0xFFFFFFFF, MAGIC, MAGIC2))
            if N < 1:
                raise ValueError("%s: bad N = %d" % (path, N))
            self.magic = magic
            self.scale = 0
            self.hdr = 8
            if magic == MAGIC2:
                sc = struct.unpack("<i", f.read(4))[0]
                if not (1 <= sc <= 8):
                    raise ValueError("%s: bad scale %d" % (path, sc))
                self.scale = sc
                self.hdr = 12
            self.N = N
            self._build_index()
            g = array("d")
            g.fromfile(f, self.gtotal)
            r = array("d")
            r.fromfile(f, self.rtotal)
            if sys.byteorder != "little":
                g.byteswap()
                r.byteswap()
            self._G = g
            self._R = r
            self.mmap = False
        want = self.hdr + 8 * (self.gtotal + self.rtotal)
        got = os.path.getsize(path)
        if got != want:
            raise ValueError("%s: size %d, expected %d" % (path, got, want))

    def _init_mmap(self, path):
        import mmap as _mmap
        self._fh = open(path, "rb")
        magic, N = struct.unpack("<ii", self._fh.read(8))
        if magic not in (MAGIC, MAGIC2):
            raise ValueError("%s: bad magic 0x%08x" % (path, magic & 0xFFFFFFFF))
        self.magic = magic
        self.scale = 0
        self.hdr = 8
        if magic == MAGIC2:
            sc = struct.unpack("<i", self._fh.read(4))[0]
            if not (1 <= sc <= 8):
                raise ValueError("%s: bad scale %d" % (path, sc))
            self.scale = sc
            self.hdr = 12
        self.N = N
        self._build_index()
        self._mm = _mmap.mmap(self._fh.fileno(), 0, access=_mmap.ACCESS_READ)
        want = self.hdr + 8 * (self.gtotal + self.rtotal)
        if len(self._mm) != want:
            raise ValueError("%s: size %d, expected %d" % (path, len(self._mm), want))
        self._roff = self.hdr + 8 * self.gtotal
        if sys.byteorder != "little":
            raise ValueError("mmap mode needs a little-endian host")

    class _MMView(object):
        """Minimal read-only sequence view over a slice of the mapping."""
        __slots__ = ("mm", "base", "n")

        def __init__(self, mm, base, n):
            self.mm, self.base, self.n = mm, base, n

        def __len__(self):
            return self.n

        def __iter__(self):
            return iter(struct.unpack_from("<%dd" % self.n, self.mm, self.base))

        def tolist(self):
            return list(struct.unpack_from("<%dd" % self.n, self.mm, self.base))

        def __getitem__(self, i):
            if isinstance(i, slice):
                return self.tolist()[i]
            if i < 0:
                i += self.n
            if not (0 <= i < self.n):
                raise IndexError("row index %d out of range (length %d)" % (i, self.n))
            return struct.unpack_from("<d", self.mm, self.base + 8 * i)[0]

    def close(self):
        if getattr(self, "mmap", False):
            self._mm.close()
            self._fh.close()

    # ---------------------------------------------------------------- index
    def _build_index(self):
        N = self.N
        # pair (l,a) -> flat index; qbase[pair] = offset of (l,a,q=0) in R
        pstart = [0] * (N + 2)
        np_ = 0
        for l in range(1, N + 1):
            pstart[l] = np_
            np_ += N - l + 1
        pstart[N + 1] = np_
        qbase = [0] * np_
        off = 0
        nrows = 0
        for l in range(1, N + 1):
            for a in range(0, N - l + 1):
                qbase[pstart[l] + a] = off
                Q = N - l - a
                off += _pref(a, Q + 1)
                nrows += Q + 1
        self._pstart = pstart
        self._qbase = qbase
        self.rtotal = off
        self.nrows = nrows
        gbase = [0] * (N + 1)
        g = 0
        for p in range(0, N + 1):
            gbase[p] = g
            g += N - p + 1
        self._gbase = gbase
        self.gtotal = g

    def in_range_r(self, l, a, q):
        return (1 <= l <= self.N and a >= 0 and q >= 0 and l + a + q <= self.N)

    def r_row_index(self, l, a, q):
        """Index inside the R block of the first entry (s = 0) of row (l,a,q)."""
        if not self.in_range_r(l, a, q):
            raise IndexError("R row (l=%d,a=%d,q=%d) outside the table (N=%d)"
                             % (l, a, q, self.N))
        return self._qbase[self._pstart[l] + a] + _pref(a, q)

    def r_index(self, l, a, q, s):
        """Index inside the R block of the entry R_{l,a}(q,s).

        Raises IndexError if s is outside the stored support; use R() for the
        zero-extended value."""
        n = slen(a, q)
        if not (0 <= s < n):
            raise IndexError("s=%d outside the support {0..%d} of R_{%d,%d}(%d,.)"
                             % (s, n - 1, l, a, q))
        return self.r_row_index(l, a, q) + s

    def g_index(self, p, q):
        if not (0 <= p <= self.N and 0 <= q <= self.N - p):
            raise IndexError("G(p=%d,q=%d) outside the table (N=%d)" % (p, q, self.N))
        return self._gbase[p] + q

    def file_offset_g(self, p, q):
        """Byte offset in the file of the double G(p,q)."""
        return self.hdr + 8 * self.g_index(p, q)

    def file_offset_r(self, l, a, q, s):
        """Byte offset in the file of the double R(l,a,q,s)."""
        return self.hdr + 8 * (self.gtotal + self.r_index(l, a, q, s))

    # ---------------------------------------------------------------- values
    def G(self, p, q):
        """G_{(p,q)}; 0.0 outside 0 <= p, 0 <= q, p+q <= N."""
        if p < 0 or q < 0 or p + q > self.N:
            return 0.0
        i = self._gbase[p] + q
        if self.mmap:
            return struct.unpack_from("<d", self._mm, self.hdr + 8 * i)[0]
        return self._G[i]

    def R(self, l, a, q, s):
        """R_{l,a}(q,s), zero-extended outside the stored support.

        The convention R_{0,a}(q,s) = [a == 0][q == s] (the identity kernel
        K_0) is included, since the sampler needs it."""
        if l == 0:
            return 1.0 if (a == 0 and q == s) else 0.0
        if l < 0 or a < 0 or q < 0 or s < 0:
            return 0.0
        if s >= slen(a, q):
            return 0.0
        if l + a + q > self.N:
            # Not stored in this table.  Return 0.0 like the C++ reader
            # (avr_table.hpp); callers needing such entries must build a
            # table with a larger N.
            return 0.0
        i = self.r_row_index(l, a, q) + s
        if self.mmap:
            return struct.unpack_from("<d", self._mm, self._roff + 8 * i)[0]
        return self._R[i]

    def K(self, l, p, q, c, t):
        """The unreduced kernel K_l((p,q),(c,t)) = R_{l,p-c}(q,t) for c <= p."""
        if c > p or c < 0:
            return 0.0
        return self.R(l, p - c, q, t)

    # ------------------------------------------------- unscaled (true) values
    #
    # For an AVR1 table (scale == 0) these are the identity.  For an AVR2
    # table the stored double is multiplied by 2^{scale*grade}; the product is
    # exact, so no accuracy is lost -- only the binary64 exponent range can be
    # exceeded, and then an exact Python int is returned instead of a float.

    def _unscale(self, x, grade):
        """x * 2^{scale*grade} as a float, or as an exact int/Fraction when
        that overflows binary64.  Exact in every case (power-of-two scaling)."""
        k = self.scale * grade
        if k == 0 or x == 0.0:
            return x
        try:
            return math.ldexp(x, k)
        except OverflowError:
            pass
        m, e = math.frexp(x)                 # x = m * 2^e, 0.5 <= |m| < 1
        num = int(math.ldexp(m, 53))         # exact integer mantissa
        sh = e - 53 + k
        if sh >= 0:
            return num << sh                 # exact int
        return Fraction(num, 1 << (-sh))     # exact rational

    def R_true(self, l, a, q, s):
        """R_{l,a}(q,s) unscaled: a float when representable in binary64,
        otherwise an exact Python int (or Fraction below 1)."""
        v = self.R(l, a, q, s)
        if l == 0 or self.scale == 0:
            return v
        return self._unscale(v, l + a + q)

    def G_true(self, p, q):
        """G_{(p,q)} unscaled (float when representable, else exact int)."""
        return self._unscale(self.G(p, q), p + q)

    def R_exact(self, l, a, q, s):
        """R_{l,a}(q,s) unscaled as a Fraction (always exact)."""
        v = self.R(l, a, q, s)
        if l == 0 or self.scale == 0:
            return Fraction(v)
        return Fraction(v) * (Fraction(2) ** (self.scale * (l + a + q)))

    def G_exact(self, p, q):
        """G_{(p,q)} unscaled as a Fraction (always exact)."""
        v = self.G(p, q)
        if self.scale == 0:
            return Fraction(v)
        return Fraction(v) * (Fraction(2) ** (self.scale * (p + q)))

    def g_ratio(self, p1, q1, p2, q2):
        """G_{(p1,q1)} / G_{(p2,q2)} as a float, with the scale factors applied.

        Ratios of table entries of *different* grade need the scale factor;
        this helper is the safe way to form them (the masses differ by a few
        units in every use, so 2.0 ** (scale*dm) never overflows)."""
        b = self.G(p2, q2)
        if b == 0.0:
            return float("inf") if self.G(p1, q1) else float("nan")
        r = self.G(p1, q1) / b
        if self.scale:
            r *= 2.0 ** (self.scale * ((p1 + q1) - (p2 + q2)))
        return r

    def r_ratio(self, l1, a1, q1, s1, l2, a2, q2, s2):
        """R_{l1,a1}(q1,s1) / R_{l2,a2}(q2,s2) with the scale factors applied."""
        b = self.R(l2, a2, q2, s2)
        if b == 0.0:
            return float("inf") if self.R(l1, a1, q1, s1) else float("nan")
        r = self.R(l1, a1, q1, s1) / b
        if self.scale:
            r *= 2.0 ** (self.scale * ((l1 + a1 + q1) - (l2 + a2 + q2)))
        return r

    def r_row(self, l, a, q):
        """The stored row R_{l,a}(q,.) as a list of slen(a,q) doubles."""
        i = self.r_row_index(l, a, q)
        n = slen(a, q)
        if self.mmap:
            return AvrTable._MMView(self._mm, self._roff + 8 * i, n)
        return self._R[i:i + n]

    def terms(self, nmax=None):
        """[G(n,0) for n = 0..nmax] -- the stored (possibly scaled) values."""
        if nmax is None:
            nmax = self.N
        return [self.G(n, 0) for n in range(nmax + 1)]

    def terms_true(self, nmax=None):
        """[G_true(n,0) for n = 0..nmax] -- the unscaled |Av_n(12453)|
        (float where representable, exact int beyond that)."""
        if nmax is None:
            nmax = self.N
        return [self.G_true(n, 0) for n in range(nmax + 1)]

    # ------------------------------------------------------------ iteration
    def iter_r(self, max_grade=None):
        """Yield (l, a, q, s, value) in file order."""
        N = self.N
        W = N if max_grade is None else min(max_grade, N)
        R = self._R if not self.mmap else None
        for l in range(1, N + 1):
            for a in range(0, N - l + 1):
                base_a = self._qbase[self._pstart[l] + a]
                for q in range(0, N - l - a + 1):
                    if l + a + q > W:
                        continue
                    i = base_a + _pref(a, q)
                    n = slen(a, q)
                    if R is None:
                        vals = struct.unpack_from("<%dd" % n, self._mm,
                                                  self._roff + 8 * i)
                    else:
                        vals = R[i:i + n]
                    for s in range(n):
                        yield (l, a, q, s, vals[s])


# --------------------------------------------------------------------- CLI

M64 = (1 << 64) - 1


def _probe(T, seed, count):
    """Reproduces avr_check.cpp's --probe stream bit for bit (xorshift64*)."""
    st = seed & M64
    N = T.N

    def nxt():
        nonlocal st
        st ^= st >> 12
        st = (st ^ (st << 25)) & M64
        st ^= st >> 27
        return (st * 2685821657736338717) & M64

    out = []
    for _ in range(count):
        l = 1 + nxt() % N
        a = nxt() % (N - l + 1)
        q = nxt() % (N - l - a + 1)
        s = nxt() % slen(a, q)
        out.append("R %d %d %d %d %.17g" % (l, a, q, s, T.R(l, a, q, s)))
        p = nxt() % (N + 1)
        qq = nxt() % (N - p + 1)
        out.append("G %d %d %.17g" % (p, qq, T.G(p, qq)))
    sys.stdout.write("\n".join(out) + "\n")


def _fmt(x):
    return repr(float(x))


def main(argv):
    import argparse
    ap = argparse.ArgumentParser(description="read an AVR1 table file")
    ap.add_argument("file")
    ap.add_argument("--info", action="store_true", help="print header and sizes")
    ap.add_argument("--G", action="append", default=[], metavar="p,q",
                    help="print G(p,q) (repeatable)")
    ap.add_argument("--R", action="append", default=[], metavar="l,a,q,s",
                    help="print R(l,a,q,s) (repeatable)")
    ap.add_argument("--row", action="append", default=[], metavar="l,a,q",
                    help="print the whole row R_{l,a}(q,.) (repeatable)")
    ap.add_argument("--terms", metavar="A:B", default=None,
                    help="print n and G(n,0) for n = A..B")
    ap.add_argument("--index", action="append", default=[], metavar="l,a,q,s",
                    help="print the R index and file byte offset of an entry")
    ap.add_argument("--dump-r", metavar="OUT", default=None,
                    help="write 'l a q s value' for every stored entry")
    ap.add_argument("--max-grade", type=int, default=None,
                    help="with --dump-r: only rows of grade l+a+q <= W")
    ap.add_argument("--eps", type=float, default=0.0,
                    help="with --dump-r: skip entries with |value| <= eps")
    ap.add_argument("--true", action="store_true",
                    help="with --terms/--G/--R: print the unscaled value")
    ap.add_argument("--mmap", action="store_true",
                    help="read through a shared mmap instead of loading into RAM")
    ap.add_argument("--probe", nargs=2, metavar=("SEED", "COUNT"), default=None,
                    help="print the same deterministic probe list as "
                         "'avr_check FILE --probe SEED COUNT' (xorshift64*)")
    args = ap.parse_args(argv)

    T = AvrTable(args.file, use_mmap=args.mmap)
    if args.probe:
        _probe(T, int(args.probe[0]), int(args.probe[1]))
        return 0
    if args.info or not (args.G or args.R or args.row or args.terms
                         or args.index or args.dump_r):
        print("file        %s" % T.path)
        print("magic       %s (0x%08x)" % ("AVR2" if T.scale else "AVR1", T.magic))
        print("scale       %d   (stored = true * 2^{-%d*grade})" % (T.scale, T.scale))
        print("header      %d bytes" % T.hdr)
        print("N           %d" % T.N)
        print("G entries   %d" % T.gtotal)
        print("R rows      %d" % T.nrows)
        print("R entries   %d" % T.rtotal)
        print("bytes       %d" % (T.hdr + 8 * (T.gtotal + T.rtotal)))
        print("a_N = G(N,0)  %s   (stored)" % _fmt(T.G(T.N, 0)))
        if T.scale:
            print("a_N unscaled  %s" % T.G_true(T.N, 0))
    for spec in args.G:
        p, q = (int(x) for x in spec.split(","))
        print("G(%d,%d) = %s" % (p, q, T.G_true(p, q) if args.true else _fmt(T.G(p, q))))
    for spec in args.R:
        l, a, q, s = (int(x) for x in spec.split(","))
        print("R(%d,%d,%d,%d) = %s" % (l, a, q, s,
              T.R_true(l, a, q, s) if args.true else _fmt(T.R(l, a, q, s))))
    for spec in args.row:
        l, a, q = (int(x) for x in spec.split(","))
        row = T.r_row(l, a, q)
        print("R(%d,%d,%d,.) [%d] = %s" % (l, a, q, len(row), " ".join(_fmt(v) for v in row)))
    for spec in args.index:
        l, a, q, s = (int(x) for x in spec.split(","))
        print("R(%d,%d,%d,%d): r_index %d, file byte offset %d"
              % (l, a, q, s, T.r_index(l, a, q, s), T.file_offset_r(l, a, q, s)))
    if args.terms:
        lo, hi = (int(x) for x in args.terms.split(":"))
        for n in range(lo, min(hi, T.N) + 1):
            print("%d %s" % (n, T.G_true(n, 0) if args.true else _fmt(T.G(n, 0))))
    if args.dump_r:
        with open(args.dump_r, "w") as f:
            k = 0
            for (l, a, q, s, v) in T.iter_r(args.max_grade):
                if abs(v) > args.eps:
                    f.write("%d %d %d %d %r\n" % (l, a, q, s, float(v)))
                    k += 1
        sys.stderr.write("wrote %s (%d lines)\n" % (args.dump_r, k))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
