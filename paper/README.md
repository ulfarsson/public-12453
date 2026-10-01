# Paper

`av12453_polytime.tex` is the source of the paper, `av12453_polytime.bib` its
BibTeX database, and `av12453_polytime.pdf` the PDF built from them.  The
figures are in `figures/`: the heatmap of Figure 4 (the PermPAL rendering of
`../code/av12453_sampler/examples/ex_n300_1M.csv`, enlarged three times) and
the TikZ dot plot generated from
`../code/av12453_sampler/examples/perm_n300.txt`.

Build from this directory with

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error av12453_polytime.tex
```

The paper is distributed on arXiv (arXiv:2609.15642) under the Creative
Commons Attribution 4.0 International license (CC BY 4.0).
