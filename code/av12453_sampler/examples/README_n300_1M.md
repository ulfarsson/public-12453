# One million uniform random 12453-avoiding permutations of length 300

Date: 2026-09-03.  Produced with the scaled sampler of
code/av12453_sampler/ (commit f2807f5), table
N300s.avr (AVR2, scale 2, built by `tables --N 300 --threads 8 --scaled`,
3 h 58 min wall, 5,436,664,420 bytes; G(n,0) agrees with the known terms
for all n <= 300 within 8.9e-12 relative).

    sampler --table N300s.avr --n 300 --count 1000000 --seed 20260903 --threads 8 \
            --out perms_n300_1M.txt --binary perms_n300_1M.u16

2041.9 s on 8 threads (489.7 samples/s); the built-in avoidance check
passed on all 1,000,000 samples; the standalone checker confirmed 0
containments on the first 100,000; perms_io.py confirms the text and
binary files hold identical records and that every record is a
permutation of 1..300.

Files (SHA-256 in SHA256SUMS.txt):
- perms_n300_1M.u16    600,000,000 bytes: little-endian uint16, 300 values
                        per record, no header, values 1..300.
                        numpy: np.fromfile('perms_n300_1M.u16', dtype='<u2').reshape(-1, 300)
- perms_n300_1M.txt.gz 387 MB: the same samples as text, one permutation per
                        line (uncompressed 1,092,000,000 bytes, also kept).
- ex_n300_1M.csv        the 300 x 300 count matrix M[value][position]
                        (bottom-left origin convention documented in the
                        header comment; total 300,000,000).
- ex_n300_1M.png, ex_n300_1M_sqrt.png, ex_n300_1M_log.png
                        heatmaps with linear, sqrt and log colour scaling.

Statistics: mean number of left-to-right minima 77.485; mean position of
the maximum 53.49; mean first letter 291.91; largest cell count 70,204 (position 300, value 300; the cells with
pi_i = 300 for i <= 3 or i = 300, and pi_i = 1 for i >= 297, all have
probability a_299/a_300 and are equal up to sampling error).

The samples are uniform up to the binary64 table error (about 1e-11
relative per decision); see README_scaling.md in the sampler directory.

## PermPAL-style renderings (2026-09-13)

`ex_n300_1M_permpal.png` and `ex_n300_1M_permpal_cuberoot.png` render the
same count matrix (`ex_n300_1M.csv`) with the functions of
`vince-heatmaps.py`, the script used for the heatmaps on PermPAL, through
the driver `permpal_heatmap.py`: 300 x 300 pixels, one per cell, 8-bit
grayscale, white for an empty cell and black for the largest count
(70,204).  The first file uses `jay_adjust_mat` (square root of the count,
linear in gray; the variant PermPAL uses), the second `adjust_mat`
(cube root, piecewise linear with the mean mapped to gray level 64).
`pngcrush` was not available, so the files are written by PyPNG without
recompression; the pixels are unaffected.
