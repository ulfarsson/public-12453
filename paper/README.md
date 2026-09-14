# Paper

`av12453_polytime.tex` is the authoritative manuscript source; the checked-in
PDF is generated from it.  The BibTeX database is `av12453_polytime.bib`; keep
the two files together for local builds and journal source bundles.

Build from this directory with

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error av12453_polytime.tex
```

Before committing a regenerated PDF, inspect the log for undefined references
or citations and overfull boxes, and run the companion-code checks in
`../code/README.md`.  Build products are ignored by git.

The current PDF is the named development master, deliberately not the doubly
anonymous Combinatorial Theory review copy.  Create that derivative only when
submission preparation begins; do not remove identifying metadata from the
authoritative source.

The computational supplement cited in the data-availability section is
regenerated from `../code/`, `../notes/` and `../formal/` at submission time,
and its SHA-256 digest in the manuscript is updated then.
