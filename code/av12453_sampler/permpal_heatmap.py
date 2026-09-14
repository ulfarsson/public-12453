#!/usr/bin/env python3
"""Render the position/value count matrix of a sample in the PermPAL style.

    python3 permpal_heatmap.py COUNTS.csv -o OUT_PREFIX

COUNTS.csv is the CSV written by heatmap.py (row 0 = value n at the top of
the image, row n-1 = value 1; columns = positions 1..n).  The picture is
produced by the functions of vince-heatmaps.py, the script used for the
heatmaps on PermPAL: the counts are written to a one-line JSON file in the
layout that script reads (rows by value 1..n, columns by position), and its
`read_mat`, `jay_adjust_mat` (square-root grayscale, white = no sample,
black = the largest count; the variant PermPAL uses) and `write_png` are
applied unchanged.  `adjust_mat` (cube-root, piecewise-linear) gives a second
file OUT_PREFIX_cuberoot.png.  Requires numpy and pypng.  vince-heatmaps.py
runs `pngcrush` after writing, which only recompresses losslessly; if it is
not installed, a stand-in on PATH copies the file instead.
"""
import argparse
import json
import os
import shutil
import stat
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))


def load_vince():
    """Execute vince-heatmaps.py without its final do_all() call."""
    src = open(os.path.join(HERE, "vince-heatmaps.py")).read()
    body, sep, tail = src.rpartition("\ndo_all()")
    assert sep, "expected a trailing do_all() call in vince-heatmaps.py"
    ns = {}
    exec(compile(body + "\n", "vince-heatmaps.py", "exec"), ns)
    return ns


def read_counts_csv(path):
    rows = []
    with open(path) as f:
        for line in f:
            if line.startswith("#") or not line.strip():
                continue
            rows.append([int(x) for x in line.strip().split(",")])
    n = len(rows)
    assert all(len(r) == n for r in rows), "count matrix is not square"
    return rows                      # rows[0] is value n, rows[n-1] is value 1


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("counts_csv")
    ap.add_argument("-o", "--out", required=True, help="output path prefix")
    args = ap.parse_args(argv)
    rows = read_counts_csv(args.counts_csv)
    n = len(rows)
    total = sum(map(sum, rows))
    print(f"n={n}, {total // n} samples, largest cell {max(map(max, rows))}")

    vince = load_vince()
    out_prefix = os.path.abspath(args.out)
    with tempfile.TemporaryDirectory() as tmp:
        # JSON matrix in the layout read_mat expects: row index = value - 1
        mat_file = os.path.join(tmp, "counts.txt")
        with open(mat_file, "w") as f:
            f.write(json.dumps(rows[::-1]) + "\n")
        if shutil.which("pngcrush") is None:
            shim = os.path.join(tmp, "pngcrush")
            with open(shim, "w") as f:
                f.write('#!/bin/sh\n# stand-in for pngcrush: copy input to output\ncp "$3" "$4"\n')
            os.chmod(shim, os.stat(shim).st_mode | stat.S_IEXEC)
            os.environ["PATH"] = tmp + os.pathsep + os.environ["PATH"]
            print("pngcrush not found; copying the PNG uncompressed instead")
        cwd = os.getcwd()
        os.chdir(tmp)                # write_png uses a .temp.png in the working directory
        try:
            M = vince["read_mat"](mat_file)
            vince["write_png"](out_prefix + ".png", vince["jay_adjust_mat"](M, vince["bits"]))
            vince["write_png"](out_prefix + "_cuberoot.png", vince["adjust_mat"](M, vince["bits"]))
        finally:
            os.chdir(cwd)
    for suffix in (".png", "_cuberoot.png"):
        path = out_prefix + suffix
        print(f"wrote {os.path.relpath(path)} ({os.path.getsize(path)} bytes)")


if __name__ == "__main__":
    main()
