#!/usr/bin/env python3
"""heatmap.py -- PermPAL-style density heatmaps from a file of permutations.

Reads a text file of permutations of length n, one per line, values 1..n
separated by whitespace, accumulates the n x n matrix

    M[i][v] = #{ samples with pi_i = v }        (1-indexed i, v)

and writes:
  * a CSV dump of M
  * a PNG (pure Python: stdlib zlib for DEFLATE + a minimal hand-written
    PNG chunk writer; a hard-coded 256-entry viridis colormap; optional
    integer pixel upscaling)
  * optionally an SVG with the same picture in vector form

Orientation ("bottom-left origin", matching the permutation-diagram
convention used by PermPAL, https://permpal.com/perms/basis/0123/): the
image and CSV both have position i running left to right and value v
running bottom to top, i.e. row 0 of the *image* (top scanline) is v = n
and the last image row (bottom scanline) is v = 1.  The CSV uses the same
convention (its first written row is v = n, its last is v = 1) so that
the two files agree pixel-for-pixel / cell-for-cell; this is documented
again in a leading '#' comment line in the CSV itself.

No numpy is used or required anywhere in this file.

Also prints, over all permutations read:
  * mean number of left-to-right minima
  * mean position (1-indexed) of the value n
  * mean value of the first letter pi_1

Self-test: `python3 heatmap.py --selftest` builds a synthetic file of
identity permutations (which must produce a perfect diagonal), runs the
whole pipeline, decodes the PNG with a minimal hand-written PNG reader
(chunk framing + CRC32 + zlib inflate), and checks dimensions, checksums,
and that the diagonal/off-diagonal pixels match the colormap endpoints.
"""

import argparse
import struct
import sys
import zlib
import os
import tempfile

# --------------------------------------------------------------------------
# Hard-coded 256-entry viridis colormap (perceptually uniform, dark purple
# -> blue -> green -> yellow).  Generated once offline from the standard
# degree-6 polynomial approximation of matplotlib's viridis (Zucker/Wong
# style fit; max channel error vs. the reference LUT is a few / 255) and
# then frozen as a literal table below -- nothing computes it at runtime.
# --------------------------------------------------------------------------
VIRIDIS_256 = [
    (71,1,85),(71,3,87),(71,4,88),(71,6,89),(71,7,91),(71,8,92),(71,10,93),(71,11,95),
    (72,13,96),(72,14,97),(72,15,99),(72,17,100),(72,18,101),(72,20,103),(72,21,104),(72,22,105),
    (72,24,106),(72,25,108),(72,26,109),(72,28,110),(72,29,111),(72,31,112),(72,32,113),(72,33,114),
    (72,35,116),(72,36,117),(72,37,118),(72,39,119),(71,40,120),(71,41,121),(71,42,121),(71,44,122),
    (71,45,123),(71,46,124),(71,48,125),(70,49,126),(70,50,127),(70,51,127),(70,53,128),(70,54,129),
    (69,55,129),(69,56,130),(69,58,131),(69,59,131),(68,60,132),(68,61,133),(68,62,133),(68,63,134),
    (67,65,134),(67,66,135),(67,67,135),(66,68,136),(66,69,136),(65,70,136),(65,72,137),(65,73,137),
    (64,74,138),(64,75,138),(63,76,138),(63,77,139),(63,78,139),(62,79,139),(62,80,139),(61,81,140),
    (61,82,140),(60,84,140),(60,85,140),(59,86,140),(59,87,141),(58,88,141),(58,89,141),(57,90,141),
    (57,91,141),(56,92,141),(56,93,141),(55,94,142),(54,95,142),(54,96,142),(53,97,142),(53,98,142),
    (52,99,142),(52,100,142),(51,101,142),(50,102,142),(50,103,142),(49,104,142),(49,105,142),(48,106,142),
    (48,107,142),(47,108,142),(46,109,142),(46,110,142),(45,111,142),(45,112,142),(44,113,142),(44,114,142),
    (43,115,142),(43,116,142),(42,116,142),(41,117,142),(41,118,142),(40,119,142),(40,120,142),(39,121,142),
    (39,122,142),(38,123,142),(38,124,141),(37,125,141),(37,126,141),(37,127,141),(36,128,141),(36,129,141),
    (35,130,141),(35,131,141),(34,132,141),(34,133,141),(34,134,141),(33,134,141),(33,135,140),(33,136,140),
    (33,137,140),(32,138,140),(32,139,140),(32,140,140),(32,141,140),(31,142,140),(31,143,139),(31,144,139),
    (31,145,139),(31,146,139),(31,147,139),(31,148,139),(31,148,138),(31,149,138),(31,150,138),(31,151,138),
    (31,152,137),(31,153,137),(31,154,137),(31,155,137),(32,156,136),(32,157,136),(32,158,136),(32,159,136),
    (33,160,135),(33,161,135),(33,162,135),(34,162,134),(34,163,134),(35,164,133),(35,165,133),(36,166,133),
    (37,167,132),(37,168,132),(38,169,131),(39,170,131),(39,171,130),(40,172,130),(41,172,129),(42,173,128),
    (43,174,128),(43,175,127),(44,176,127),(45,177,126),(46,178,125),(48,179,125),(49,180,124),(50,180,123),
    (51,181,122),(52,182,122),(53,183,121),(55,184,120),(56,185,119),(58,186,118),(59,186,117),(60,187,116),
    (62,188,115),(63,189,114),(65,190,113),(67,191,112),(68,191,111),(70,192,110),(72,193,109),(74,194,108),
    (75,195,107),(77,195,105),(79,196,104),(81,197,103),(83,198,102),(85,198,100),(87,199,99),(89,200,98),
    (91,201,96),(94,201,95),(96,202,94),(98,203,92),(100,204,91),(103,204,89),(105,205,88),(107,206,86),
    (110,206,85),(112,207,83),(115,208,82),(117,208,80),(120,209,78),(122,210,77),(125,210,75),(127,211,74),
    (130,211,72),(132,212,70),(135,213,69),(138,213,67),(141,214,65),(143,214,64),(146,215,62),(149,215,61),
    (152,216,59),(154,217,57),(157,217,56),(160,218,54),(163,218,52),(166,219,51),(168,219,49),(171,220,48),
    (174,220,46),(177,220,45),(180,221,43),(183,221,42),(186,222,41),(188,222,39),(191,223,38),(194,223,37),
    (197,223,36),(200,224,35),(202,224,33),(205,225,32),(208,225,32),(210,225,31),(213,226,30),(216,226,29),
    (218,226,29),(221,227,28),(224,227,28),(226,227,27),(228,228,27),(231,228,27),(233,228,27),(236,229,27),
    (238,229,27),(240,229,28),(242,230,28),(244,230,29),(246,230,30),(248,231,31),(250,231,32),(252,231,33),
]
assert len(VIRIDIS_256) == 256


def colormap(t):
    """t in [0,1] -> (r,g,b) via the viridis LUT (nearest-index lookup)."""
    if t < 0.0:
        t = 0.0
    elif t > 1.0:
        t = 1.0
    idx = int(t * 255.0 + 0.5)
    if idx > 255:
        idx = 255
    return VIRIDIS_256[idx]


# --------------------------------------------------------------------------
# Reading permutations and accumulating the matrix
# --------------------------------------------------------------------------

def read_permutations(path, expect_n=None):
    """Yield permutations (tuples of ints, 1-indexed values) from `path`.

    Accepts both the text format (one permutation per line, values 1..n,
    space separated) and the sampler's --binary format (little-endian uint16,
    n per record, no header), which is auto-detected and needs `expect_n`.

    All lines must have the same length; if expect_n is given, every line
    must have exactly that length.  Blank lines and lines starting with
    '#' are skipped.
    """
    n = expect_n
    # the sampler's --binary format (little-endian uint16, n per record, no
    # header) is detected automatically; it needs -n, since the record length
    # is not stored in the file
    try:
        from perms_io import looks_binary, iter_binary
        binary = looks_binary(path)
    except ImportError:                      # perms_io.py not next to this file
        binary = False
    if binary:
        if n is None:
            raise ValueError(f"{path}: binary sample file; pass -n RECORD_LENGTH")
        for k, perm in enumerate(iter_binary(path, n)):
            if sorted(perm) != list(range(1, n + 1)):
                raise ValueError(f"{path}: record {k} is not a permutation of 1..{n}")
            yield tuple(perm)
        return
    with open(path, "r") as f:
        for lineno, line in enumerate(f, 1):
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split()
            try:
                perm = tuple(int(x) for x in parts)
            except ValueError:
                raise ValueError(f"{path}:{lineno}: non-integer token")
            if n is None:
                n = len(perm)
            elif len(perm) != n:
                raise ValueError(
                    f"{path}:{lineno}: expected length {n}, got {len(perm)}"
                )
            if sorted(perm) != list(range(1, n + 1)):
                raise ValueError(f"{path}:{lineno}: not a permutation of 1..{n}")
            yield perm
    if n is None:
        raise ValueError(f"{path}: no permutations found")


def accumulate(path, expect_n=None):
    """Read permutations, build M[i-1][v-1] counts (0-indexed), and stats.

    Returns (n, M, stats) where M is a list of n lists of n ints (M[pos][val])
    and stats is a dict with sample_count, mean_ltr_minima, mean_pos_of_n,
    mean_first_letter.
    """
    n = None
    M = None
    count = 0
    sum_ltr_minima = 0
    sum_pos_of_n = 0
    sum_first_letter = 0

    for perm in read_permutations(path, expect_n=expect_n):
        if n is None:
            n = len(perm)
            M = [[0] * n for _ in range(n)]
        count += 1

        # accumulate the matrix
        for i, v in enumerate(perm):
            M[i][v - 1] += 1

        # left-to-right minima
        cur_min = None
        ltr = 0
        for v in perm:
            if cur_min is None or v < cur_min:
                ltr += 1
                cur_min = v
        sum_ltr_minima += ltr

        # position of n (1-indexed)
        pos_of_n = perm.index(n) + 1
        sum_pos_of_n += pos_of_n

        # first letter
        sum_first_letter += perm[0]

    if count == 0:
        raise ValueError(f"{path}: no permutations found")

    stats = {
        "sample_count": count,
        "mean_ltr_minima": sum_ltr_minima / count,
        "mean_pos_of_n": sum_pos_of_n / count,
        "mean_first_letter": sum_first_letter / count,
    }
    return n, M, stats


# --------------------------------------------------------------------------
# CSV output
# --------------------------------------------------------------------------

def write_csv(path, n, M):
    """Write M as CSV, image-row order: first row = value n, last = value 1.

    Row r (0-indexed, 0 = first line of numeric data) is value v = n - r.
    Column c (0-indexed) is position i = c + 1.  This matches the PNG/SVG
    orientation exactly (see module docstring).
    """
    with open(path, "w") as f:
        f.write(
            "# heatmap.py CSV dump: row 0 = value {n} (top of image) .. "
            "row {nm1} = value 1 (bottom of image); "
            "col 0 = position 1 .. col {nm1} = position {n} (left to right); "
            "entry = count of samples with pi_position = value\n".format(
                n=n, nm1=n - 1
            )
        )
        for r in range(n):
            v = n - r  # value for this row, 1-indexed
            row = M_row_by_value(M, n, v)
            f.write(",".join(str(x) for x in row))
            f.write("\n")


def M_row_by_value(M, n, v):
    """Return the length-n row [count(pos=1,val=v), ..., count(pos=n,val=v)]."""
    return [M[i][v - 1] for i in range(n)]


# --------------------------------------------------------------------------
# Minimal PNG writer (stdlib zlib for DEFLATE; we build the chunk framing,
# CRC32s via zlib.crc32, and the raw scanline bytes ourselves)
# --------------------------------------------------------------------------

def _png_chunk(tag, data):
    out = struct.pack(">I", len(data))
    out += tag
    out += data
    out += struct.pack(">I", zlib.crc32(tag + data) & 0xFFFFFFFF)
    return out


def write_png(path, n, M, scale=1, norm="sqrt", vmax=None):
    """Write M as an RGB PNG, bottom-left origin, integer upscaling `scale`.

    norm in {"linear", "sqrt", "log"} controls how counts are mapped to
    [0,1] before the colormap lookup (sqrt is a reasonable default: it
    keeps a handful of very concentrated cells, e.g. near corners for
    pattern-avoiding classes, from swamping everything else in a single
    saturated pixel while still being monotone and simple).
    """
    if scale < 1:
        raise ValueError("scale must be >= 1")

    flat_max = max((v for row in M for v in row), default=0)
    if vmax is None:
        vmax = flat_max
    if vmax <= 0:
        vmax = 1

    def norm_fn(x):
        if x <= 0:
            return 0.0
        t = x / vmax
        if t > 1.0:
            t = 1.0
        if norm == "linear":
            return t
        elif norm == "sqrt":
            return t ** 0.5
        elif norm == "log":
            # log1p-style scaling normalized so t=1 -> 1
            import math

            return math.log1p(x) / math.log1p(vmax)
        else:
            raise ValueError(f"unknown norm {norm!r}")

    # Precompute one color per distinct count value 0..flat_max to avoid
    # recomputing norm_fn/colormap per pixel after upscaling.
    color_cache = [colormap(norm_fn(x)) for x in range(flat_max + 1)]

    width = n * scale
    height = n * scale

    raw = bytearray()
    for r in range(height):
        raw.append(0)  # filter type 0 (None) for every scanline
        orig_row = r // scale
        v = n - orig_row  # value for this image row (top = n, bottom = 1)
        row_counts = M_row_by_value(M, n, v)
        # expand row_counts (length n) into width pixels of RGB bytes
        line = bytearray(width * 3)
        off = 0
        for i in range(n):
            rr, gg, bb = color_cache[row_counts[i]]
            for _ in range(scale):
                line[off] = rr
                line[off + 1] = gg
                line[off + 2] = bb
                off += 3
        raw.extend(line)

    compressed = zlib.compress(bytes(raw), 9)

    ihdr = struct.pack(">IIBBBBB", width, height, 8, 2, 0, 0, 0)

    with open(path, "wb") as f:
        f.write(b"\x89PNG\r\n\x1a\n")
        f.write(_png_chunk(b"IHDR", ihdr))
        f.write(_png_chunk(b"IDAT", compressed))
        f.write(_png_chunk(b"IEND", b""))

    return width, height, vmax


# --------------------------------------------------------------------------
# Minimal PNG reader (self-test only): chunk framing + CRC32 check + zlib
# inflate + trivial unfiltering (we only ever write filter type 0).
# --------------------------------------------------------------------------

def read_png(path):
    with open(path, "rb") as f:
        data = f.read()
    if data[:8] != b"\x89PNG\r\n\x1a\n":
        raise ValueError("not a PNG (bad signature)")
    pos = 8
    width = height = bitdepth = colortype = None
    idat = bytearray()
    while pos < len(data):
        length = struct.unpack(">I", data[pos : pos + 4])[0]
        tag = data[pos + 4 : pos + 8]
        chunk_data = data[pos + 8 : pos + 8 + length]
        crc_stored = struct.unpack(">I", data[pos + 8 + length : pos + 12 + length])[0]
        crc_calc = zlib.crc32(tag + chunk_data) & 0xFFFFFFFF
        if crc_calc != crc_stored:
            raise ValueError(f"CRC mismatch in chunk {tag!r}")
        if tag == b"IHDR":
            width, height, bitdepth, colortype, comp, filt, interlace = struct.unpack(
                ">IIBBBBB", chunk_data
            )
            if comp != 0 or filt != 0 or interlace != 0:
                raise ValueError("unsupported IHDR options")
        elif tag == b"IDAT":
            idat.extend(chunk_data)
        elif tag == b"IEND":
            pos += 12 + length
            break
        pos += 12 + length

    if width is None:
        raise ValueError("missing IHDR")
    if bitdepth != 8 or colortype != 2:
        raise ValueError("reader only supports 8-bit RGB (colortype 2)")

    raw = zlib.decompress(bytes(idat))
    bpp = 3  # RGB, 8-bit
    stride = width * bpp
    pixels = [[None] * width for _ in range(height)]
    prev = bytearray(stride)
    off = 0
    for r in range(height):
        ftype = raw[off]
        off += 1
        cur = bytearray(raw[off : off + stride])
        off += stride
        if ftype == 0:
            pass
        elif ftype == 1:  # Sub
            for i in range(bpp, stride):
                cur[i] = (cur[i] + cur[i - bpp]) & 0xFF
        elif ftype == 2:  # Up
            for i in range(stride):
                cur[i] = (cur[i] + prev[i]) & 0xFF
        elif ftype == 3:  # Average
            for i in range(stride):
                a = cur[i - bpp] if i >= bpp else 0
                b = prev[i]
                cur[i] = (cur[i] + ((a + b) // 2)) & 0xFF
        elif ftype == 4:  # Paeth
            for i in range(stride):
                a = cur[i - bpp] if i >= bpp else 0
                b = prev[i]
                c = prev[i - bpp] if i >= bpp else 0
                p = a + b - c
                pa, pb, pc = abs(p - a), abs(p - b), abs(p - c)
                if pa <= pb and pa <= pc:
                    pr = a
                elif pb <= pc:
                    pr = b
                else:
                    pr = c
                cur[i] = (cur[i] + pr) & 0xFF
        else:
            raise ValueError(f"unsupported filter type {ftype}")
        for x in range(width):
            pixels[r][x] = (cur[x * 3], cur[x * 3 + 1], cur[x * 3 + 2])
        prev = cur

    return width, height, pixels


# --------------------------------------------------------------------------
# SVG output (vector alternative to the PNG)
# --------------------------------------------------------------------------

def write_svg(path, n, M, scale=8, norm="sqrt", vmax=None):
    flat_max = max((v for row in M for v in row), default=0)
    if vmax is None:
        vmax = flat_max
    if vmax <= 0:
        vmax = 1

    def norm_fn(x):
        if x <= 0:
            return 0.0
        t = x / vmax
        if t > 1.0:
            t = 1.0
        if norm == "linear":
            return t
        elif norm == "sqrt":
            return t ** 0.5
        elif norm == "log":
            import math

            return math.log1p(x) / math.log1p(vmax)
        else:
            raise ValueError(f"unknown norm {norm!r}")

    width = n * scale
    height = n * scale
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
        f'viewBox="0 0 {width} {height}" shape-rendering="crispEdges">'
    ]
    # background = colormap(0), covers empty cells in one rect
    bg = colormap(0.0)
    parts.append(
        f'<rect x="0" y="0" width="{width}" height="{height}" '
        f'fill="rgb({bg[0]},{bg[1]},{bg[2]})"/>'
    )
    for i in range(n):  # position, x axis, left to right
        for j in range(n):  # value, index j -> value v = j+1
            x = M[i][j]
            if x <= 0:
                continue
            v = j + 1
            r, g, b = colormap(norm_fn(x))
            px = i * scale
            # bottom-left origin: value 1 at the bottom, value n at the top
            py = (n - v) * scale
            parts.append(
                f'<rect x="{px}" y="{py}" width="{scale}" height="{scale}" '
                f'fill="rgb({r},{g},{b})"/>'
            )
    parts.append("</svg>")
    with open(path, "w") as f:
        f.write("\n".join(parts))
        f.write("\n")


# --------------------------------------------------------------------------
# Self-test
# --------------------------------------------------------------------------

def _selftest():
    print("heatmap.py self-test")
    n = 12
    reps = 5
    tmpdir = tempfile.mkdtemp(prefix="heatmap_selftest_")
    perm_path = os.path.join(tmpdir, "identity.txt")
    with open(perm_path, "w") as f:
        line = " ".join(str(x) for x in range(1, n + 1))
        for _ in range(reps):
            f.write(line + "\n")

    n_read, M, stats = accumulate(perm_path)
    assert n_read == n, (n_read, n)
    assert stats["sample_count"] == reps

    # identity permutation: n left-to-right minima?? no -- identity has
    # exactly 1 left-to-right minimum (pi_1 = 1 is smaller than everything
    # after it, and nothing later is smaller). Check that directly.
    assert abs(stats["mean_ltr_minima"] - 1.0) < 1e-12, stats
    assert abs(stats["mean_pos_of_n"] - n) < 1e-12, stats  # n is at position n
    assert abs(stats["mean_first_letter"] - 1.0) < 1e-12, stats

    # M must be `reps` on the diagonal M[i][i], zero elsewhere
    for i in range(n):
        for j in range(n):
            expect = reps if i == j else 0
            assert M[i][j] == expect, (i, j, M[i][j], expect)
    print(f"  matrix diagonal check OK (n={n}, reps={reps})")

    csv_path = os.path.join(tmpdir, "identity.csv")
    write_csv(csv_path, n, M)
    with open(csv_path) as f:
        csv_lines = f.readlines()
    assert csv_lines[0].startswith("#")
    data_lines = csv_lines[1:]
    assert len(data_lines) == n
    # row 0 = value n -> nonzero only in column n-1 (position n)
    row0 = [int(x) for x in data_lines[0].strip().split(",")]
    assert row0[n - 1] == reps and sum(row0) == reps, row0
    # last row = value 1 -> nonzero only in column 0 (position 1)
    rowlast = [int(x) for x in data_lines[-1].strip().split(",")]
    assert rowlast[0] == reps and sum(rowlast) == reps, rowlast
    print("  CSV orientation check OK")

    scale = 3
    png_path = os.path.join(tmpdir, "identity.png")
    width, height, vmax = write_png(png_path, n, M, scale=scale, norm="linear")
    assert width == n * scale and height == n * scale
    assert vmax == reps

    w2, h2, pixels = read_png(png_path)
    assert (w2, h2) == (width, height), (w2, h2, width, height)
    print(f"  PNG decode OK: {w2}x{h2}, chunk CRCs verified by read_png")

    hot = colormap(1.0)  # normalized count 1.0 -> brightest color
    cold = colormap(0.0)  # empty cell -> darkest color
    # Diagonal cell (position i, value i), 0-indexed i, sits at image
    # row (n-1-i)*scale .. and column i*scale (bottom-left origin).
    for i in range(n):
        img_row = (n - 1 - i) * scale + (scale // 2)
        img_col = i * scale + (scale // 2)
        px = pixels[img_row][img_col]
        assert px == hot, (i, px, hot)
    # an off-diagonal cell, e.g. position 1 (col 0), value n (top row)
    # is empty unless n == 1.
    if n > 1:
        px = pixels[0 + scale // 2][0 + scale // 2]
        assert px == cold, (px, cold)
    print("  PNG pixel-placement / bottom-left-origin check OK")

    svg_path = os.path.join(tmpdir, "identity.svg")
    write_svg(svg_path, n, M, scale=4, norm="linear")
    with open(svg_path) as f:
        svg_text = f.read()
    assert svg_text.startswith("<svg")
    assert svg_text.strip().endswith("</svg>")
    assert svg_text.count("<rect") == n + 1  # n diagonal cells + background
    print("  SVG sanity check OK")

    print(f"All self-tests passed. (scratch dir: {tmpdir})")


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------

def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Build a PermPAL-style density heatmap from a file of permutations."
    )
    ap.add_argument("perm_file", nargs="?",
                    help="file of permutations: text (one per line) or the sampler's "
                         "--binary format (little-endian uint16, n per record; needs -n)")
    ap.add_argument("-o", "--out", default=None, help="output path prefix (default: perm_file basename)")
    ap.add_argument("-n", type=int, default=None, help="expected permutation length (validated)")
    ap.add_argument("--scale", type=int, default=None, help="integer pixel upscale factor (default: auto, aiming for >=512px)")
    ap.add_argument("--norm", choices=["linear", "sqrt", "log"], default="sqrt", help="count -> color normalization (default: sqrt)")
    ap.add_argument("--svg", action="store_true", help="also write an SVG version")
    ap.add_argument("--svg-scale", type=int, default=None, help="pixels-per-cell for the SVG (default: same policy as PNG scale)")
    ap.add_argument("--no-png", action="store_true", help="skip PNG output")
    ap.add_argument("--no-csv", action="store_true", help="skip CSV output")
    ap.add_argument("--selftest", action="store_true", help="run the built-in self-test and exit")
    args = ap.parse_args(argv)

    if args.selftest:
        _selftest()
        return 0

    if not args.perm_file:
        ap.error("perm_file is required unless --selftest is given")

    out_prefix = args.out or os.path.splitext(os.path.basename(args.perm_file))[0]

    n, M, stats = accumulate(args.perm_file, expect_n=args.n)

    scale = args.scale
    if scale is None:
        scale = max(1, (512 + n - 1) // n) if n > 0 else 1
    svg_scale = args.svg_scale if args.svg_scale is not None else max(1, min(scale, 16))

    print(f"n = {n}")
    print(f"samples = {stats['sample_count']}")
    print(f"mean number of left-to-right minima = {stats['mean_ltr_minima']:.6f}")
    print(f"mean position of n (the largest value)  = {stats['mean_pos_of_n']:.6f}")
    print(f"mean first letter (pi_1)                = {stats['mean_first_letter']:.6f}")

    if not args.no_csv:
        csv_path = out_prefix + ".csv"
        write_csv(csv_path, n, M)
        print(f"wrote {csv_path}")

    if not args.no_png:
        png_path = out_prefix + ".png"
        width, height, vmax = write_png(png_path, n, M, scale=scale, norm=args.norm)
        print(f"wrote {png_path} ({width}x{height}, scale={scale}, norm={args.norm}, max cell count={vmax})")

    if args.svg:
        svg_path = out_prefix + ".svg"
        write_svg(svg_path, n, M, scale=svg_scale, norm=args.norm)
        print(f"wrote {svg_path} (scale={svg_scale}, norm={args.norm})")

    return 0


if __name__ == "__main__":
    sys.exit(main())
