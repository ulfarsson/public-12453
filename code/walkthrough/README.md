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

Sections covered, in the paper's order and numbering: Section 1
(containment, occurrences, the family beta_d, the first terms); Section 2's
preamble (standardization, restriction, d-triggers, Lemma 2.1 with the
231-obligations); 2.1 (Lemma 2.2 and Av(231)(I), direct sums and display (3),
Example 2.3, Definition 2.4 implemented for every d as `legal_move`/`scan`,
Lemma 2.5, Example 2.6, Lemma 2.7 checked along the running example for
d = 1, 2, and Proposition 2.8 checked along the running example for d = 1, 2
and exhaustively for small n); 2.2 (Lemma 2.7 at d = 1 with the stack rebuilt
from the prefix, Example 2.9 reproduced as a table); 2.3 (Proposition 2.10's
recurrence W implemented and compared with permuta, Examples 2.11 and
2.12).  The rest of the paper is not walked through.  Finite instances of
its statements are checked by the script described below.

## Exhaustive checks up to length 8

`av12453_exhaustive_checks.py` compares finite instances of the paper's
numbered statements, and of the unnumbered claims after `eq:rho`, Theorem 4.3
and Lemma 7.2 (the path counts for every state, the dictionary to
Biers-Ariel's program, the translation for every `d`), with brute-force
computations from the definitions, including exhaustive checks on the
permutations of length at most 8 (option `--nmax`).  Each check prints the
range of parameters it covers and what it leaves out: the general family is
checked for `d <= 3` (for `d <= 4` in the coefficients), the factorization
`K_UV = K_U K_V` through single heads and products applied to the empty-stack
values, and Proposition 8.1 on the literal recurrence rather than on the
stored tables.  The checks are grouped
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
