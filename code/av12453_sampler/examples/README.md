# The data behind the paper's Figure 4

| file | contents |
|---|---|
| `ex_n300_1M.csv` | the 300 x 300 position/value count matrix of 1,000,000 uniform random permutations in `Av_300(12453)`, as written by `heatmap.py` (the header comment gives the orientation: row 0 is value 300, column 0 is position 1); every row and every column sums to 1,000,000 |
| `ex_n300_1M_permpal.png` | the heatmap of that matrix drawn by `vince-heatmaps.py`, the script used for the heatmaps on PermPAL, through `permpal_heatmap.py`: 300 x 300 pixels, one per cell, 8-bit grayscale, white for an empty cell and black for the largest count, gray level linear in the square root of the count (`jay_adjust_mat`) |
| `perm_n300.txt` | one of these permutations, the dot plot of the figure |

The paper's `figures/heatmap_n300_1M_permpal.png` is `ex_n300_1M_permpal.png`
enlarged three times by pixel replication, and its `figures/perm_n300_tikz.tex`
was generated from `perm_n300.txt` by `plot_perm.py --tikz`.

## How the samples were drawn

The table was the scaled `N = 300` table (`AVR2`, 5,436,664,420 bytes),
built in 3 h 58 min on 8 threads by

    ./tables --N 300 --threads 8 --scaled --out N300s.avr

and the samples were drawn in 2,042 s on 8 threads by

    ./sampler --table N300s.avr --n 300 --count 1000000 --seed 20260903 --threads 8 \
              --out perms_n300_1M.txt --binary perms_n300_1M.u16

The sampler's built-in avoidance test passed on every sample.  The sample
files themselves (600 MB in the binary form) are not part of the repository.
`perm_n300.txt` is record 65167 (counting from 0) of `perms_n300_1M.u16`,
chosen by `random.Random(20260912).randrange(1000000)` in Python.  The
samples are uniform up to the floating-point error bounded in Appendix A of
the paper (total variation below `3.5e-5`).

To redraw the figure from a sample file:

    python3 heatmap.py perms_n300_1M.txt -o ex_n300_1M     # writes ex_n300_1M.csv (and a viridis PNG)
    python3 permpal_heatmap.py ex_n300_1M.csv -o ex_n300_1M_permpal
    python3 plot_perm.py perm_n300.txt -o perm_n300 --tikz perm_n300_tikz.tex

(`permpal_heatmap.py` needs `numpy` and `pypng`, and it also writes a
cube-root variant, `*_cuberoot.png`.)

## Statistics of the sample

Mean number of left-to-right minima 77.485, mean position of the maximum
53.49, mean first letter 291.91.  The largest cell count is 70,204, at
position 300 and value 300.  The cells with `pi_i = 300` for `i <= 3` or
`i = 300`, and with `pi_i = 1` for `i >= 297`, all have probability
`a_299/a_300`, and their counts agree up to sampling error.
