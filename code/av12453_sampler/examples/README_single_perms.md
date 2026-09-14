# Four single uniform random 12453-avoiding permutations

Date: 2026-09-12.  Dot plots `perm_n50.png`, `perm_n100.png`,
`perm_n150.png`, `perm_n300.png` (900 x 900 pixels, position left to right,
value bottom to top, the orientation of the heatmaps) of one uniformly
random permutation of `Av_n(12453)` for `n = 50, 100, 150, 300`, each with
the permutation itself on one line in the matching `.txt` file.

- `n = 50, 100, 150`: drawn by `sampler` from an unscaled N=150 table
  (`tables --N 150 --threads 8`, AVR1, 342,167,216 bytes, 1 min 43 s wall)
  with `--count 1` and seeds 20260911, 20260912, 20260913 respectively.
- `n = 300`: record 65167 (0-based) of the one-million-sample file
  `perms_n300_1M.u16` described in `README_n300_1M.md`, chosen as
  `random.Random(20260912).randrange(1000000)` in Python.

Plotted with `python3 plot_perm.py perm_nN.txt -o examples/perm_nN`; all
four permutations pass `avoid_check` (0 of 4 contain 12453).
