# AV(12453) computational supplement

The publication supplement is the public companion repository: the `code/`,
`formal/` and `paper/` directories together with `LICENSE`, `CITATION.cff`
and a `MANIFEST.sha256` of individual file digests.  It is generated from the
development repository at submission time, archived at a permanent URL, and
the manuscript's data-availability section records the archive's name and
SHA-256 digest.

From the archive root:

```sh
sha256sum -c MANIFEST.sha256
cd code
```

Then follow `code/README.md` (fast checks, CRT reconstruction, the `n=300`
engine, the sampler and heatmaps) and `formal/README.md` (building and
auditing the Lean certificate).  The AVX-512 production program is
platform-specific; the Python reference checks, reconstruction and asymptotic
holdout use only the Python standard library, and the scalar C++ paths need a
C++20 compiler.
