# Walkthrough of the paper with permuta

`av12453_walkthrough.py` follows the paper section by section and lets a
reader run its examples, and their own permutations, through the definitions
and results.  It is meant for reading and experimenting; the fast
implementations are elsewhere in `code/`.

Requirements: Python 3 and [permuta](https://github.com/PermutaTriangle/Permuta)
(`pip install permuta`; version 2.3.1 was used).  Run the whole file with
`python3 av12453_walkthrough.py`, or open it in VS Code, Spyder or Jupyter
(via Jupytext) and execute it cell by cell; the `# %%` markers delimit cells.

Conventions: the paper's 1-based one-line notation is used for input and
output through the helpers `P(...)` and `show(...)`; permuta is 0-based
internally, and the conversion happens only in those helpers.

Sections covered so far, in the paper's order and numbering: Section 1
(containment, occurrences, the family beta_d, the first terms); Section 2's
preamble (standardization, restriction, d-triggers, Lemma 2.1 with the
231-obligations, residual obligations); 2.1 (Lemma 2.2 and Av(231)(I), direct
sums and display (3), Example 2.3, Definition 2.4 implemented for every d as
`legal_move`/`scan`, Example 2.7 with `is_scan_state` and `is_faithful`, Lemma 2.8 and Example 2.9,
Proposition 2.10 checked along
the running example for d = 1, 2 and exhaustively for small n); 2.2 (Lemma 2.11
checked, Example 2.12 reproduced as a table); 2.3 (Proposition 2.13's
recurrence W implemented and compared with permuta, Examples 2.14 and
2.15).  Next:
2.4 to 2.6 (the exponential state space, the protected-tail factorization,
the scalar kernels) and Sections 3 to 5.

## Exhaustive checks up to length 8

`av12453_exhaustive_checks.py` checks every numbered statement of the paper
that has finite content for all permutations of length at most 8 (option
`--nmax`), by comparing the paper's constructions and displayed formulas
with brute-force computations from the definitions.  The checks are grouped
by section in `checks/sec2.py` (Section 2), `checks/sec345.py` (Sections 3
to 5) and `checks/sec678.py` (Sections 6 to 8 and 10); `checks/common.py`
holds the shared brute-force helpers (permuta for permutations and pattern
containment, transcriptions of the definitions for everything else).  The
fast implementations in `code/` are not used.  Statements without finite
content (complexity bounds, the abstract factorization theorem in its
generality, the certification of `n = 150`, the asymptotic conjecture) are
listed as such with the finite instance they imply.  Run under PyPy for
speed:

    pypy3 av12453_exhaustive_checks.py

(the PyPy virtual environment is created with `pypy3 -m venv venv-pypy` and
`pip install permuta`).  The script prints one line per statement with the
number of comparisons and exits with status 1 if any check fails.
