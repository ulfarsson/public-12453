#!/usr/bin/env python3
"""avr_mine.py -- a second, independently written reader for the AVR1/AVR2 tables.

It is written from the file-format description at the top of tables.cpp
and shares no code with the production readers avr_table.py and
avr_table.hpp, so that the checks built on it (pair_law.py, prefix_law.py)
do not inherit an indexing error of those readers.  The layout is found by
walking the documented nesting order and recording where each row starts,
not by the closed-form offsets the production readers use.

File format (little-endian):

    AVR1   int32 magic 0x41565231, int32 N
    AVR2   int32 magic 0x41565232, int32 N, int32 scale
    then   G doubles for p = 0..N, q = 0..N-p            (nested in that order)
           R doubles for l = 1..N, a = 0..N-l, q = 0..N-l-a,
                         s = 0..slen(a,q)-1             (nested in that order)

An AVR2 file stores R_{l,a}(q,s) * 2^{-scale*(l+a+q)} and G_{(p,q)} *
2^{-scale*(p+q)}.  Unlike avr_table.py, G() and Rrow() here return the
UNSCALED values (the counts themselves) as floats.  Unscaling multiplies by a
power of two and is exact; it raises OverflowError for an entry whose count
exceeds the binary64 range, which happens only beyond grade about 260.

The whole file is read into memory, so the reader is meant for tables up to
N of about 150.

    from avr_mine import Avr, slen
    T = Avr("N40s.avr");  T.G(10, 0);  T.Rrow(3, 1, 2)
"""
import math
import struct

AVR1 = 0x41565231
AVR2 = 0x41565232


def slen(a, q):
    """Number of stored terminal coordinates of the row R_{l,a}(q,.)."""
    return q + 1 if a == 0 else a + q


class Avr(object):
    def __init__(self, path):
        with open(path, "rb") as f:
            data = f.read()
        magic = int.from_bytes(data[0:4], "little")
        N = int.from_bytes(data[4:8], "little", signed=True)
        if magic == AVR1:
            scale, pos = 0, 8
        elif magic == AVR2:
            scale, pos = int.from_bytes(data[8:12], "little", signed=True), 12
        else:
            raise ValueError("%s: magic 0x%08x is neither AVR1 nor AVR2" % (path, magic))
        if N < 1 or scale < 0:
            raise ValueError("%s: bad header N=%d scale=%d" % (path, N, scale))
        self.N, self.scale, self._data = N, scale, data
        self._g = {}
        for p in range(N + 1):
            for q in range(N - p + 1):
                self._g[(p, q)] = struct.unpack_from("<d", data, pos)[0]
                pos += 8
        self._row = {}
        for l in range(1, N + 1):
            for a in range(N - l + 1):
                for q in range(N - l - a + 1):
                    self._row[(l, a, q)] = pos
                    pos += 8 * slen(a, q)
        if pos != len(data):
            raise ValueError("%s: layout ends at byte %d but the file has %d bytes"
                             % (path, pos, len(data)))
        self._cache = {}

    def _unscale(self, x, grade):
        if self.scale == 0 or x == 0.0:
            return x
        return math.ldexp(x, self.scale * grade)

    def G(self, p, q):
        """G_{(p,q)}, unscaled; 0.0 outside 0 <= p, 0 <= q, p + q <= N."""
        v = self._g.get((p, q))
        if v is None:
            return 0.0
        return self._unscale(v, p + q)

    def Rrow(self, l, a, q):
        """The row R_{l,a}(q,.), unscaled, as a list of slen(a,q) floats, or
        None when the row is not stored (l < 1 or grade l + a + q > N)."""
        key = (l, a, q)
        r = self._cache.get(key)
        if r is not None:
            return r
        off = self._row.get(key)
        if off is None:
            return None
        k = slen(a, q)
        g = l + a + q
        r = [self._unscale(v, g) for v in struct.unpack_from("<%dd" % k, self._data, off)]
        self._cache[key] = r
        return r
