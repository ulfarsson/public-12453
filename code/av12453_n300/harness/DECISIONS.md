# Decisions made while building the harness (2026-09-02)

Recorded per the standing instruction to note ambiguity resolutions rather
than stop and ask, since the work ran unattended.

## 1. Synthetic reconstruct.py test prime counts

The task brief says: "generate residue files for N = 150 ... for, say, 12
primes below 2^16 and 4 below 2^21, run reconstruct.py, and confirm it
reproduces the data file exactly."

Taken literally, 12 primes below 2^16 (~16 bits each) plus 4 below 2^21
(~21 bits each) is only ~276 bits of product -- far short of the 558-bit
bound B_150 that primary primes must exceed to reconstruct correctly
(confirmed both by my own bona_bound.py and by
repo/code/reconstruct_av12453_rns.py's docstring, "The first 18 primes are
used for CRT reconstruction through n=150", 18*31=558). With only 16 small
primes, reconstruct.py's own bound check would correctly refuse to run
("primary CRT product does not exceed exact bound"), which contradicts
"confirm it reproduces the data file exactly."

Resolution: read "12 ... and 4 ..." as specifying WITHHELD/redundant primes
of each size, not the whole primary set. test/make_synthetic_residues.py
computes the actual required primary count from the real bound (currently
36 primes below 2^16 for N=150) and adds exactly 12 more below 2^16 and 4
below 2^21 as independent withheld checks, so both the letter (12-and-4
mix of the two sizes) and the mathematical requirement (product > B_150)
are satisfied. See test/make_synthetic_residues.py's module docstring.

## 2. run_all.sh binary contract

The GEMM engine that run_all.sh drives is being built as a separate work
item and did not exist at the time this harness was written. The brief's
"Arithmetic" section says primes are a compile-time `-DMODP=...` choice
(matching the existing av12453_homog_split.cpp pattern), which implies one
compiled binary per prime rather than one binary taking a runtime prime
argument. run_all.sh therefore assumes: one binary per prime, path built by
substituting `{bindir}`/`{prime}` into a `--pattern` template (default
`{bindir}/av12453_gemm_{prime}`), invoked as
`BIN --n N --threads K --out OUTFILE`, writing the residue file and exiting
0 iff all built-in checks passed. Both the naming pattern and the
invocation line are clearly marked and trivially editable in run_all.sh if
the real engine's CLI differs. Verified with a stub engine
(test/stub_engine.py) rather than the real one; see REPORT.md.

## 3. Prime-size file naming (primes_u16.txt / primes_u32.txt)

The brief's two build variants are named by *storage width* (u16, u32), not
literally by the primes' own bit length: design (a) uses primes p < 2^21
stored as u32 ("About 55 primes for n = 300"), design (b) uses primes
p < 2^16 stored as u16 ("About 72 primes"). primes.py follows that
convention: primes_u32.txt holds primes below 2^21 (not below 2^32), and
primes_u16.txt holds primes below 2^16.

## 4. Withheld-check count for the N=300 recommended sets

primes.py defaults to 6 withheld primes per size class (matching the brief:
"a recommended set with 6 withheld check primes"), independently for both
the u16 and the u32 build, since only one build will actually be run and
each needs its own full withheld set.
