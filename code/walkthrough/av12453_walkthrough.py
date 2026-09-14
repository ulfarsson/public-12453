# %% [markdown]
# # Walkthrough of the paper with permuta
#
# A companion to *Protected tails and polynomial-time enumeration of
# permutations avoiding a direct sum of an increasing pattern and 231*.  It
# lets a reader run the paper's examples, and their own permutations, through
# the definitions and results, section by section and in the paper's order and
# vocabulary.  It is written for reading and experimenting, not for speed; the
# fast implementations live elsewhere in `code/`.
#
# Requirements: Python 3 and `permuta` (`pip install permuta`).  Run the whole
# file (`python3 av12453_walkthrough.py`) or execute it cell by cell; the
# `# %%` markers are recognised by VS Code, Spyder and Jupytext.
#
# Notation.  The paper writes permutations in one-line notation with values
# 1..n, for example 251796834, and positions 1..n.  permuta stores values and
# positions 0-based.  All conversion happens in the helpers below: build a
# permutation from the paper's notation with `P("251796834")`, a word with
# `word("11 10 14 12 13 15")`, and print in the paper's notation with `show`.
# Positions reported by `occurrences` are converted to 1-based as well.  The
# numbers of lemmas, propositions and examples refer to the current manuscript.

# %%
from functools import lru_cache
from itertools import permutations

from permuta import Av, Perm


def word(one_line):
    """A word with distinct entries as a tuple of 1-based values.

    Accepts a string of digits ("251796834"), a space-separated string
    ("11 10 14 12 13 15") or any iterable of positive integers.  Unlike a
    permutation, a word need not use every value 1..n.
    """
    if isinstance(one_line, str):
        parts = one_line.split() if " " in one_line else list(one_line)
        values = tuple(int(v) for v in parts)
    else:
        values = tuple(one_line)
    if len(set(values)) != len(values):
        raise ValueError(f"repeated entry in {values}")
    return values


def P(one_line):
    """A permuta Perm from the paper's 1-based one-line notation."""
    values = word(one_line)
    if sorted(values) != list(range(1, len(values) + 1)):
        raise ValueError(f"not a permutation of 1..n: {values}")
    return Perm.one_based(values)


def show(perm_or_word):
    """The paper's notation: digits when every value is <= 9, else spaced.

    Accepts a permuta Perm (0-based, converted) or a word (already 1-based).
    """
    if isinstance(perm_or_word, Perm):
        values = [v + 1 for v in perm_or_word]
    else:
        values = list(perm_or_word)
    if all(v <= 9 for v in values):
        return "".join(str(v) for v in values)
    return " ".join(str(v) for v in values)


def occurrences(perm, patt):
    """All occurrences of `patt` in `perm`: 1-based positions and the entries."""
    for idx in patt.occurrences_in(perm):
        positions = tuple(i + 1 for i in idx)
        entries = tuple(perm[i] + 1 for i in idx)
        yield positions, entries


# %% [markdown]
# ## Section 1.  Introduction
#
# A permutation pi *contains* a pattern tau if some entries of pi, read left
# to right, have the same relative order as tau; otherwise pi *avoids* tau.
# The introduction's example is the pattern 12453 and the permutation
# 251796834, in which the entries 2, 5, 7, 9, 6 have relative ranks 1, 2, 4,
# 5, 3 and so form an occurrence of 12453.

# %%
tau = P("12453")
pi = P("251796834")
print("pattern  tau =", show(tau))
print("permutation pi =", show(pi))
print("pi contains tau:", pi.contains(tau))
print("pi avoids tau:  ", pi.avoids(tau))

# %% [markdown]
# permuta lists every occurrence as a tuple of positions.  We print each one
# in the paper's convention together with the entries it uses; the occurrence
# named in the introduction, at positions 1, 2, 4, 5, 6, is the only one.

# %%
occs = list(occurrences(pi, tau))
print(f"{len(occs)} occurrence(s) of {show(tau)} in {show(pi)}:")
for positions, entries in occs:
    print("  positions", positions, "entries", entries)

# %% [markdown]
# The paper studies the family beta_d = iota_d (+) 231, the direct sum of the
# increasing pattern of length d and 231 (display (1)).  The direct sum writes
# the first pattern and then the second with every value increased by the
# length of the first; permuta provides it as `Perm.direct_sum` (also `+`).

# %%
def beta(d):
    """beta_d = iota_d (+) 231."""
    return Perm.monotone_increasing(d) + P("231")


for d in range(1, 5):
    print(f"beta_{d} = {show(beta(d))}")
assert beta(2) == tau

# %% [markdown]
# `Av_n(tau)` is the set of tau-avoiding permutations of length n.  permuta's
# `Av` builds a class length by length rather than by filtering: every avoider
# of length n+1 arises from an avoider of length n by appending a final entry,
# and the values that may be appended are worked out from the shorter members
# already generated, so that only the pattern itself has to be filtered out, at
# the one length where the basis lives.  The counts
# reproduce the first terms displayed in the introduction, display (2):
# 1, 1, 2, 6, 24, 119, 694, 4581, 33286, ...  This is quick for small n and
# transparent, but the number of permutations to generate grows like
# (9 + 4 sqrt 2)^n = 14.66^n, the growth rate of Av(12453) determined by Bona;
# the paper's algorithm is what makes n = 150 possible.

# %%
first_terms = [1, 1, 2, 6, 24, 119, 694, 4581, 33286]
counts = Av([tau]).enumeration(8)
for n, count in enumerate(counts):
    print(f"|Av_{n}(12453)| = {count}")
assert counts == first_terms, counts

# %% [markdown]
# ## Section 2.  Triggers, stacks, and the complete one-threshold prototype
#
# ### Standardization, restriction, and d-triggers
#
# For a word w with distinct entries, its *standardization* st(w) replaces the
# smallest entry by 1, the next smallest by 2, and so on.  If X is a set of
# values, w|_X is the subword of w formed by the entries that lie in X.  An
# *increasing d-subsequence* of a permutation, or of a word with distinct
# entries, is a choice of positions i_1 < ... < i_d with increasing entries;
# its last entry is a *d-trigger*.

# %%
def standardize(w):
    """st(w) as a permuta Perm."""
    return Perm.to_standard(word(w))


def restrict(w, X):
    """w|_X: the subword of w formed by the entries lying in the set X."""
    return tuple(v for v in word(w) if v in X)


def triggers(pi, d):
    """The d-triggers of the permutation pi as (position, value) pairs, 1-based,
    in reading order: the last entries of the occurrences of 12...d."""
    iota_d = Perm.monotone_increasing(d)
    last_positions = sorted({idx[-1] for idx in iota_d.occurrences_in(pi)})
    return [(i + 1, pi[i] + 1) for i in last_positions]


def lis_ending(w):
    """For each position of the word w, the length of the longest increasing
    subsequence ending there (a letter is a d-trigger iff this is >= d)."""
    w = word(w)
    best = []
    for j, x in enumerate(w):
        best.append(1 + max((best[i] for i in range(j) if w[i] < x), default=0))
    return best


def trigger_values(w, d):
    """The d-triggers of a word (any distinct-entry prefix), as values in
    reading order."""
    w = word(w)
    return [x for x, l in zip(w, lis_ending(w)) if l >= d]


w = word("11 10 14 12 13 15")  # the projection of the running example's first letter
print("w        =", show(w))
print("st(w)    =", show(standardize(w)))
print("w|_{>12} =", show(restrict(w, {v for v in w if v > 12})))
example = P("316829574")  # the paper's example after the least-trigger lemma (Section 3)
print("pi =", show(example))
for d in (1, 2, 3):
    print(f"  {d}-triggers (position, value):", triggers(example, d))
assert [v for _, v in triggers(example, 2)] == trigger_values("316829574", 2)

# %% [markdown]
# For d = 1 every letter is a trigger.  For d = 2 in the example above, the
# entries 3, 6 form an increasing 2-subsequence, so 6 is a 2-trigger; 3 and 1
# are not, since nothing smaller precedes them.  The running example of the
# paper, display (4), has the triggers below; it is scanned for d = 1 in
# Example 2.12 and for d = 2 in Example 4.2.

# %%
running = P("9 11 10 14 5 12 6 2 3 8 4 7 1 13 15")
running_list = list(word("9 11 10 14 5 12 6 2 3 8 4 7 1 13 15"))
for d in (1, 2, 3):
    print(f"{d}-triggers of the running example:", [v for _, v in triggers(running, d)])

# %% [markdown]
# ### Lemma 2.1 (trigger lemma) and the 231-obligations
#
# When a d-trigger c = pi_j is read, the *projection* it creates is the word
# pi_{j+1} ... pi_n |_{x > c}, the later entries larger than c.  The
# *231-obligation* of c is that this word avoid 231 after standardization.
# Lemma 2.1: pi avoids beta_d if and only if every d-trigger's obligation is
# satisfied.  `obligations` checks all of them and shows a witness when one
# fails.

# %%
def projection(pi, position):
    """The projection created by the entry at `position` (1-based): the later
    entries larger than it, as a word."""
    c = pi[position - 1] + 1
    return tuple(v + 1 for v in pi[position:] if v + 1 > c)


def obligations(pi, d, verbose=True):
    """Check the 231-obligation of every d-trigger of pi; True when all hold."""
    all_ok = True
    for position, c in triggers(pi, d):
        proj = projection(pi, position)
        std = standardize(proj) if proj else Perm(())
        ok = std.avoids(P("231"))
        all_ok = all_ok and ok
        if verbose:
            print(f"  {d}-trigger {c} at position {position}: projection {show(proj) or '(empty)'}"
                  f" = st {show(std) or '(empty)'}: avoids 231? {ok}")
        if verbose and not ok:
            idx = next(P("231").occurrences_in(std))
            witness = tuple(proj[i] for i in idx)
            iota_occ = next(o for o in Perm.monotone_increasing(d).occurrences_in(pi)
                            if o[-1] == position - 1)
            prefix = tuple(pi[i] + 1 for i in iota_occ)
            print(f"    231 occurrence {show(witness)} in the projection; with the increasing"
                  f" {d}-subsequence {show(prefix)} ending at {c} it forms the {show(beta(d))}"
                  f" occurrence {show(prefix + witness)}")
    return all_ok


# %% [markdown]
# The running example avoids 12453, and every one of its eleven 2-triggers has
# a 231-avoiding projection.  The introduction's 251796834 contains 12453: its
# 2-trigger 5 (preceded by the smaller 2) has projection 7, 9, 6, 8, whose
# standardization 2413 contains 231 through 7, 9, 6, and prefixing 2, 5
# recovers the occurrence 2, 5, 7, 9, 6 of Section 1.  It is the only failing
# trigger.

# %%
print(show(running), "avoids 12453:", running.avoids(tau))
print("all 2-trigger obligations satisfied:", obligations(running, 2))
print(show(pi), "avoids 12453:", pi.avoids(tau))
print("all 2-trigger obligations satisfied:", obligations(pi, 2))

# %% [markdown]
# Lemma 2.1 is an equivalence, so avoidance of beta_d and satisfaction of all
# obligations agree on every permutation; the cell checks this for all
# permutations of length 7 and d = 1, 2, 3.

# %%
for d in (1, 2, 3):
    agree = all(sigma.avoids(beta(d)) == obligations(sigma, d, verbose=False)
                for sigma in Perm.of_length(7))
    print(f"d = {d}: Lemma 2.1 agrees with direct avoidance on all 5040 permutations of length 7: {agree}")
    assert agree

# %% [markdown]
# ### Residual obligations of a scanned prefix
#
# While a permutation is read left to right, the obligation of a trigger c
# already read is only partly decided.  If sigma = sigma_1 ... sigma_k is the
# read prefix, c = sigma_j, the letters of [n] not in sigma are *unread*, and
# w is a *completion* of sigma (a word using each unread letter once), then w
# satisfies the *residual obligation* of c when
# (sigma_{j+1} ... sigma_k w)|_{x > c} avoids 231 after standardization.
# `residual` lists the orders of the unread projection letters that satisfy
# this, by trying them all (fine for a handful of letters).

# %%
def avoids_231(w):
    """Does the word w avoid 231 (after standardization)?"""
    w = word(w)
    return not w or standardize(w).avoids(P("231"))


def residual(prefix, n, position):
    """The residual obligation of the trigger at `position` (1-based) of the
    scanned `prefix` of a permutation of [n]: returns (fixed, unread, allowed),
    the scanned projection letters, the unread projection letters, and the
    orders of the unread ones that keep the projection 231-avoiding."""
    prefix = word(prefix)
    c = prefix[position - 1]
    fixed = tuple(v for v in prefix[position:] if v > c)
    unread = tuple(v for v in range(c + 1, n + 1) if v not in prefix)
    allowed = [w for w in permutations(unread) if avoids_231(fixed + w)]
    return fixed, unread, allowed


# %% [markdown]
# For d = 2, after the prefix 9 11 10 14 5 12 of the running example the
# 2-triggers read are 11, 10, 14 and 12.  For the trigger 11 the scanned
# projection letters are 14 and 12 and the unread ones 13 and 15; only 13
# before 15 keeps 14 12 13 15 free of 231.  The trigger 10 imposes the same
# condition, the triggers 14 and 12 none.  For d = 1, after the prefix 9 11,
# the trigger 9 has one scanned projection letter, 11, and five unread ones,
# of whose 120 orders only 14 are allowed: 10 must come first, and the rest
# must avoid 231 (the Catalan number C_4 = 14).  This is the first-letter
# lemma (Lemma 2.2) at work; it is stated in 2.1 below.

# %%
prefix = word("9 11 10 14 5 12")
for position, c in triggers(running, 2):
    if position > len(prefix):
        break
    fixed, unread, allowed = residual(prefix, 15, position)
    print(f"trigger {c} at position {position}: fixed {show(fixed) or '(none)'}, unread {show(unread) or '(none)'};"
          f" allowed orders:", [show(w) for w in allowed] or ["(no condition)"])
fixed, unread, allowed = residual("9 11", 15, 1)
print(f"trigger 9 after the prefix 9 11: fixed {show(fixed)}, unread {show(unread)},"
      f" {len(allowed)} allowed orders out of {len(list(permutations(unread)))};"
      f" all start with 10: {all(w[0] == 10 for w in allowed)}")

# %% [markdown]
# ### 2.1  The Catalan interval stack
#
# **Lemma 2.2 (first-letter lemma).**  It concerns permutations of an arbitrary
# finite set of values I, words using each value of I once; such a word avoids
# 231 when its standardization does.  Let x in I have local rank r, that is,
# r = |{y in I : y <= x}|.  A permutation of I beginning with x avoids 231 if
# and only if all values below x occur before all values above x and the two
# induced subwords avoid 231.  Reading x thus replaces an interval of size l by
# intervals of sizes r-1 and l-r, in that order (zero parts deleted).
# Av(231)(I) denotes the 231-avoiding words using each value of I once; it
# has C_|I| elements whatever the values are.

# %%
def av231(I):
    """Av(231)(I): all 231-avoiding words using each value of I once."""
    return [w for w in permutations(sorted(I)) if avoids_231(w)]


def first_letter_split(I, x):
    """The lower and upper parts into which reading x splits the interval I."""
    lower = tuple(y for y in sorted(I) if y < x)
    upper = tuple(y for y in sorted(I) if y > x)
    return lower, upper


I = (10, 12, 13, 14, 15)
for w in ("10 12 15 13 14", "12 15 10 13 14"):
    print(f"{w}: st = {show(standardize(w))}; avoids 231? {avoids_231(w)}")
print("Av(231)({3, 7, 8}) =", [show(w) for w in av231((3, 7, 8))])
print("|Av(231)(I)| for I = {10, 12, 13, 14, 15}:", len(av231(I)), "(C_5 = 42)")
for x in I:
    lower, upper = first_letter_split(I, x)
    r = len(lower) + 1
    by_lemma = sorted((x,) + u + v for u in av231(lower) for v in av231(upper))
    by_brute_force = sorted(w for w in av231(I) if w[0] == x)
    assert by_lemma == by_brute_force
    print(f"x = {x} (local rank {r}): parts of sizes {r - 1} and {len(I) - r};"
          f" {len(by_lemma)} words of Av(231)(I) begin with {x}")

# %% [markdown]
# **Direct sums and the stack of one projection, display (3).**  If I < J and
# u, w are words on I and J, then u (+) w is the concatenation uw; for sets of
# words, (+) is the set of all concatenations.  Reading the projection of one
# trigger letter by letter, Lemma 2.2 splits the active head at each letter,
# and the letter itself then plays no further role; the unread projection
# letters must form a word in Av(231)(I_1) (+) ... (+) Av(231)(I_s), display
# (3).  `stack_of_projection` performs this scan for one projection.

# %%
def oplus(A, B):
    """A (+) B for sets of words A on I and B on J with I < J."""
    for u in A:
        for w in B:
            assert not u or not w or max(u) < min(w), "the value sets are not ordered"
    return [u + w for u in A for w in B]


def language(stack):
    """Av(231)(I_1) (+) ... (+) Av(231)(I_s) for a stack given as a list of
    tuples; the empty word for the empty stack."""
    words = [()]
    for I in stack:
        words = oplus(words, av231(I))
    return words


def stack_of_projection(values, letters_read):
    """The interval stack after reading `letters_read` (in order) from the
    projection whose unread values are `values`."""
    stack = [tuple(sorted(values))]
    for x in letters_read:
        head = stack[0]
        assert x in head, f"{x} is not in the active head {head}"
        lower, upper = first_letter_split(head, x)
        stack = [part for part in (lower, upper) if part] + stack[1:]
    return stack


def show_stack(stack):
    return " | ".join("{" + ",".join(map(str, I)) + "}" for I in stack) or "(empty)"


# %% [markdown]
# **Example 2.3 (reading one projection).**  For the running example and
# d = 1, the first letter 9 is a trigger whose projection 11 10 14 12 13 15 is
# read at positions 2, 3, 4, 6, 14, 15.  At every step the brute-force
# residual obligation of the trigger 9 equals the language of display (3).

# %%
proj_positions = [i + 1 for i, v in enumerate(running_list) if i > 0 and v > 9]
proj_values = [running_list[i - 1] for i in proj_positions]
print("projection of the trigger 9:", show(proj_values), "read at positions", proj_positions)
for k in range(len(proj_positions) + 1):
    stack = stack_of_projection(proj_values, proj_values[:k])
    prefix = running_list[: (proj_positions[k - 1] if k else 1)]
    _, unread, allowed = residual(prefix, 15, 1)
    assert sorted(language(stack)) == sorted(allowed)
    just_read = f"after reading {proj_values[k - 1]}" if k else "before any projection letter"
    print(f"{just_read:32s} stack {show_stack(stack):26s} {len(allowed):3d} allowed orders = "
          + (" * ".join(str(len(av231(I))) for I in stack) or "1 (empty stack)"))

# %% [markdown]
# **Definition 2.4 (scan states and legal moves).**  A *scan state* is a pair
# (sigma, S): the read prefix sigma and the stack S = (I_1, ..., I_s), a list
# of nonempty sets with I_1 < ... < I_s whose union is the set of unread
# letters above the least d-trigger of sigma (empty when there is none).
# Let x be unread and q the least d-trigger of sigma when there is one.
# Reading x is a *legal move* in exactly three cases:
# (a) *merger*: x is a d-trigger of sigma x smaller than every d-trigger of
#     sigma; E is the set of unread letters strictly between x and q (all
#     unread letters above x when sigma has no d-trigger), and the new stack is
#     (E u I_1, I_2, ..., I_s), or (E) when s = 0, empty sets deleted;
# (b) *split*: x is a d-trigger of sigma x exceeding some d-trigger of sigma,
#     and x lies in I_1, which it replaces by its parts below and above x,
#     empty sets deleted (an endpoint or an interior choice according to the
#     local rank of x);
# (c) *non-trigger move*: x is not a d-trigger of sigma x; the stack is
#     unchanged (impossible for d = 1).
# Every other letter is *illegal*.  A word is *legal* if it is reached from
# the initial state (empty prefix, empty stack) by legal moves; its stack S is
# then determined by sigma and written S(sigma), and R(sigma) is the set of
# permutations with prefix sigma all of whose prefixes are legal.  For a
# scan state an illegal letter is exactly a letter of a deferred interval
# I_2, ..., I_s (Lemma 2.5).  `legal_move` implements the three
# cases, `scan` reads a prefix move by move, and `S` returns the stack of a
# legal prefix.

# %%
def legal_move(prefix, stack, x, n, d):
    """The legal move reading x from the scan state (prefix, stack), as
    (kind, new_stack), or None if reading x is illegal."""
    prefix = word(prefix)
    if x in prefix or not 1 <= x <= n:
        raise ValueError(f"{x} is not an unread letter")
    old_triggers = trigger_values(prefix, d)
    q = min(old_triggers) if old_triggers else None
    unread = [v for v in range(1, n + 1) if v not in prefix and v != x]
    x_is_trigger = lis_ending(prefix + (x,))[-1] >= d
    if x_is_trigger and (q is None or x < q):                       # (a) merger
        E = tuple(v for v in unread if x < v and (q is None or v < q))
        if stack:
            new = [tuple(sorted(E + stack[0]))] + stack[1:]
        else:
            new = [E] if E else []
        return "merger", new
    if x_is_trigger and stack and x in stack[0]:                     # (b) split
        lower, upper = first_letter_split(stack[0], x)
        kind = "split, interior choice" if lower and upper else "split, endpoint choice"
        return kind, [part for part in (lower, upper) if part] + stack[1:]
    if not x_is_trigger:                                             # (c) non-trigger move
        return "non-trigger move", stack
    return None                                                      # illegal


def scan(prefix, n, d, verbose=False):
    """Read `prefix` from the initial state; returns the list of stacks after
    each letter (the stack of the empty prefix first).  Raises ValueError at
    the first illegal letter."""
    prefix = word(prefix)
    stacks = [[]]
    for k, x in enumerate(prefix):
        move = legal_move(prefix[:k], stacks[-1], x, n, d)
        if move is None:
            raise ValueError(f"{show(prefix[:k + 1])}: reading {x} is illegal from the stack "
                             f"{show_stack(stacks[-1])}")
        kind, new = move
        if verbose:
            print(f"read {x:2d}: {kind:24s} {show_stack(stacks[-1]):30s} -> {show_stack(new)}")
        stacks.append(new)
    return stacks


def is_legal(prefix, n, d):
    try:
        scan(prefix, n, d)
        return True
    except ValueError:
        return False


def S(prefix, n, d):
    """S(sigma): the stack of a legal prefix."""
    return scan(prefix, n, d)[-1]


def is_scan_state(prefix, stack, n, d):
    """Definition 2.4: the stack is a list of nonempty sets, increasing, whose
    union is the set of unread letters above the least d-trigger of the prefix
    (empty when there is none)."""
    prefix = word(prefix)
    trig = trigger_values(prefix, d)
    expected = {v for v in range(1, n + 1) if v not in prefix and trig and v > min(trig)}
    if any(not I for I in stack):
        return False
    if any(max(I) >= min(J) for I, J in zip(stack, stack[1:])):
        return False
    return {v for I in stack for v in I} == expected


# %% [markdown]
# For d = 1 every letter is a trigger, so a legal move is a new left-to-right
# minimum (a merger) or a letter of the active head (a split).  Scanning the
# running example for d = 1 shows both, and reading 15 after 9 11 10 14 5 12,
# a letter of the deferred interval {15}, is illegal.

# %%
scan("9 11 10 14 5 12", 15, 1, verbose=True)
try:
    scan("9 11 10 14 5 12 15", 15, 1)
except ValueError as e:
    print("illegal move detected:", e)

# %% [markdown]
# **Lemma 2.5 (legal moves) and Definition 2.6 (faithful stacks).**  A legal
# move from a scan state leads to a scan state, and a letter is illegal exactly
# when it lies in a deferred interval.  The stack S of a scan state (sigma, S)
# is *faithful to* sigma if a completion of sigma satisfies the residual
# obligations of all d-triggers of sigma exactly when its restriction to the
# stack lies in Av(231)(I_1) (+) ... (+) Av(231)(I_s).  `is_faithful` tests
# this by brute force, comparing the stack's language with the orders of the
# unread letters above the least trigger that satisfy every residual
# obligation (`conjunction_allowed`, defined below with Proposition 2.10).
#
# **Example 2.7 (faithful and unfaithful stacks).**  For the prefix
# 9 11 10 14 of the running example and d = 1, the unread letters above the
# least trigger 9 are 12, 13, 15, so ({12,13},{15}), ({12,13,15}) and
# ({12},{13},{15}) all form scan states with the prefix.  Only the first is
# faithful: the completions satisfying every obligation read 12 and 13 in
# either order before 15; the stack ({12,13,15}) also allows 15,12,13, which
# violates the obligation of 9 (14,15,12 is a 231), and ({12},{13},{15})
# forbids 13,12,15, which satisfies every obligation.

# %%
def conjunction_allowed(prefix, n, d):
    """Orders of the unread letters above the least d-trigger of `prefix` that
    satisfy the residual obligations of all d-triggers read (brute force)."""
    prefix = word(prefix)
    trig = trigger_values(prefix, d)
    if not trig:
        return [()]
    q = min(trig)
    unread = tuple(v for v in range(q + 1, n + 1) if v not in prefix)
    allowed = []
    for w in permutations(unread):
        ok = True
        for position, c in enumerate(prefix, start=1):
            if c not in trig:
                continue
            fixed = tuple(v for v in prefix[position:] if v > c)
            future = tuple(v for v in w if v > c)
            if not avoids_231(fixed + future):
                ok = False
                break
        if ok:
            allowed.append(w)
    return allowed


def is_faithful(prefix, stack, n, d):
    """Definition 2.6, by brute force: the stack's language equals the set of
    orders of the unread letters above the least trigger that satisfy the
    residual obligations of all d-triggers of the prefix."""
    assert is_scan_state(prefix, stack, n, d), "not a scan state"
    return sorted(language(stack)) == sorted(conjunction_allowed(prefix, n, d))


sigma = "9 11 10 14"
print("allowed orders of 12, 13, 15 after", sigma, ":", [show(w) for w in conjunction_allowed(sigma, 15, 1)])
for stack in ([(12, 13), (15,)], [(12, 13, 15)], [(12,), (13,), (15,)]):
    print(f"  {show_stack(stack):22s} scan state? {is_scan_state(sigma, stack, 15, 1)}  faithful? {is_faithful(sigma, stack, 15, 1)}")
assert S(sigma, 15, 1) == [(12, 13), (15,)] and is_faithful(sigma, S(sigma, 15, 1), 15, 1)

# %% [markdown]
# **Lemma 2.8 (stack merger).**  Let S be faithful to sigma and let x be a
# d-trigger of sigma x smaller than every d-trigger of sigma.
# (a) If sigma has no d-trigger, then S is empty and (E), with E the unread
#     letters above x, is faithful to sigma x.
# (b) If sigma has a d-trigger q, let E be the unread letters strictly between
#     x and q; then E is empty or an interval, E < I_1 and E u I_1 is an
#     interval when s >= 1, and the merged stack (E u I_1, I_2, ..., I_s) is
#     faithful to sigma x.  Only the active head changes (Figure 1).
# Faithfulness is exercised in the Proposition 2.10(a) cell below, where the
# prefix 9 11 10 14 5 with stack {6,7,8,12,13} | {15} has 42 = C_5 C_1 allowed
# orders.
#
# **Example 2.9 (one merger).**  After 9 11 10 14 the stack is {12,13} | {15};
# the fifth letter 5 is a trigger smaller than 9, 11, 10, 14, so q = 9 and
# E = {6,7,8}, and the merged stack is {6,7,8,12,13} | {15}.  The read letters
# 9, 10, 11 lie between 6, 7, 8 and 12 in value but create no separation.

# %%
kind, merged = legal_move("9 11 10 14", S("9 11 10 14", 15, 1), 5, 15, 1)
print("reading 5 after 9 11 10 14:", kind, "->", show_stack(merged))
assert merged == [(6, 7, 8, 12, 13), (15,)]

# %% [markdown]
# **Proposition 2.10 (scan states of avoiders).**  For a legal prefix sigma with
# stack S(sigma) = (I_1, ..., I_s):
# (a) S(sigma) is faithful to sigma: a completion satisfies the residual
#     obligations of all d-triggers of sigma iff its restriction to the stack
#     lies in the language of (3);
# (b) an illegal letter leaves no beta_d-avoiding completion;
# (c) R(sigma) is the set of beta_d-avoiders with prefix sigma; in particular
#     R(empty) = Av_n(beta_d), and legal = prefix of an avoider.
# The next cells check that S(sigma) is a scan state (Lemma 2.5(a)) and
# faithful (part (a)) along the running example for d = 1 and d = 2 (the
# d = 2 stacks printed are the interval-stack column of Example 4.2), and (c),
# with (b) as its consequence, for d = 1, 2, 3 at n <= 7 and for d = 1, 2 at
# n = 6.

# %%
for d in (1, 2):
    print(f"--- d = {d}")
    stacks = scan(running_list, 15, d)
    for k in range(1, 16):
        prefix = running_list[:k]
        stack = stacks[k]
        assert is_scan_state(prefix, stack, 15, d), ("Lemma 2.5(a) fails", d, k)
        assert is_faithful(prefix, stack, 15, d), ("(a) fails", d, k)
        brute = conjunction_allowed(prefix, 15, d)
        print(f"prefix {show(prefix):40s} stack {show_stack(stack):30s} {len(brute):4d} allowed orders")

# %% [markdown]
# Parts (b) and (c): for every permutation of length n <= 7 and d = 1, 2, 3,
# all prefixes are legal exactly when the permutation avoids beta_d, so that
# R(empty) = Av_n(beta_d).  For n = 6 and d = 1, 2 the legal words over [6] are
# exactly the prefixes of avoiders: 'legal implies prefix of an avoider' is the
# second half of (c), and its converse gives (b), since a letter extending a
# legal prefix to a word that is a prefix of no avoider is illegal.

# %%
for d in (1, 2, 3):
    for n in range(1, 8):
        readable = {show(sigma) for sigma in Perm.of_length(n) if is_legal([v + 1 for v in sigma], n, d)}
        avoiders = {show(sigma) for sigma in Av([beta(d)]).of_length(n)}
        assert readable == avoiders, (d, n)
    print(f"d = {d}: R(empty) = Av_n(beta_{d}) for all n <= 7"
          f" (|Av_7| = {len(readable)})")
n = 6
for d in (1, 2):
    prefixes_of_avoiders = {tuple(v + 1 for v in sigma)[:k]
                            for sigma in Av([beta(d)]).of_length(n) for k in range(n + 1)}
    legal_words = {w for k in range(n + 1) for w in permutations(range(1, n + 1), k)
                   if is_legal(w, n, d)}
    assert legal_words == prefixes_of_avoiders
    print(f"d = {d}, n = {n}: the legal words are exactly the prefixes of avoiders ({len(legal_words)} words)")

# %% [markdown]
# ### 2.2  The one-threshold state
#
# For d = 1 the least trigger is the minimum m of the prefix, the stack is the
# set of unread letters above m (Definition 2.4), and the state is written
# W_p(L) with p the number of unread letters below m and L the interval sizes.
# **Lemma 2.11 (separations of the one-threshold stack).**  Call two unread
# values *adjacent* when no unread value lies strictly between them.  After a
# legal prefix has been read, adjacent unread letters u < v above m lie in
# different intervals iff some letter x with u < x < v was read after a letter
# smaller than u.  Hence the stack can be recovered from the prefix alone: its
# values are the unread letters above m, cut into blocks at exactly the
# adjacent pairs of the lemma (`stack_by_lemma`).  The cell checks both at
# every prefix of the running example and at every prefix of every
# 1342-avoiding permutation of length 6 (the legal prefixes, by Proposition
# 2.9(c)), and shows the counterexample to dropping adjacency: after 3 5 1 of
# [7], the non-adjacent 2 and 6 lie in different intervals although no letter
# between them was read after a letter below 2.

# %%
def separated_by_lemma(prefix, u, v):
    """Lemma 2.11's criterion: some x with u < x < v was read after a letter
    smaller than u."""
    prefix = word(prefix)
    return any(u < prefix[j] < v and any(prefix[i] < u for i in range(j))
               for j in range(len(prefix)))


def different_intervals(stack, u, v):
    return next(I for I in stack if u in I) != next(I for I in stack if v in I)


def stack_by_lemma(prefix, n):
    """The stack rebuilt from the prefix alone, as Lemma 2.11 allows."""
    prefix = word(prefix)
    m = min(prefix)
    above = sorted(v for v in range(m + 1, n + 1) if v not in prefix)
    blocks, current = [], []
    for u, v in zip(above, above[1:] + [None]):
        current.append(u)
        if v is None or separated_by_lemma(prefix, u, v):
            blocks.append(tuple(current))
            current = []
    return blocks


def check_lemma_2_8(prefix, n):
    prefix = word(prefix)
    stack = S(prefix, n, 1)
    m = min(prefix)
    above = sorted(v for v in range(m + 1, n + 1) if v not in prefix)
    for u, v in zip(above, above[1:]):  # adjacent unread letters above m
        if different_intervals(stack, u, v) != separated_by_lemma(prefix, u, v):
            return False
    return stack_by_lemma(prefix, n) == stack


assert all(check_lemma_2_8(running_list[:k], 15) for k in range(1, 16))
assert all(check_lemma_2_8(tuple(v + 1 for v in sigma)[:k], 6)
           for sigma in Av([beta(1)]).of_length(6) for k in range(1, 7))
print("Lemma 2.11 holds, and rebuilds the stack, at every prefix of the running example"
      " and of every 1342-avoider of length 6")
stack_351 = S("351", 7, 1)
print("after the prefix 3 5 1 of [7] the stack is", show_stack(stack_351),
      f"; for the non-adjacent pair 2, 6: different intervals? {different_intervals(stack_351, 2, 6)};"
      f" separated by the lemma's criterion? {separated_by_lemma('351', 2, 6)}")

# %% [markdown]
# **Example 2.12 (a one-threshold scan).**  The full d = 1 scan of the running
# example, with the move (in the table's names: every new minimum is a merger,
# written 'new minimum, merger' when it adjoins values or creates the stack
# and 'new minimum' when E is empty; an endpoint choice in a head of size one
# is 'head exhausted'), the minimum m, the stack and the state W_p(L).  It
# reproduces the paper's table row by row, which the cell asserts.

# %%
def state_d1(prefix, stack):
    """The one-threshold state (p, L) of a legal prefix: p unread letters
    below the minimum m, and the interval sizes L."""
    m = min(prefix)
    p = sum(1 for v in range(1, m) if v not in prefix)
    return p, tuple(len(I) for I in stack)


def paper_label(kind, old_stack, new_stack):
    """The move names used in the paper's table of Example 2.12: every new
    minimum is a merger, written 'new minimum, merger' when it adjoins values
    or creates the stack and 'new minimum' when E is empty; an endpoint choice
    in a head of size one is 'head exhausted'."""
    if kind == "merger":
        grew = bool(new_stack) and len(new_stack[0]) > (len(old_stack[0]) if old_stack else 0)
        return "new minimum, merger" if grew else "new minimum"
    if kind == "split, endpoint choice":
        return "head exhausted" if len(old_stack[0]) == 1 else "endpoint choice"
    return "interior choice"


stacks = scan(running_list, 15, 1)
labels = []
print(f"{'i':>2} {'pi_i':>4}  {'move':20s} {'m':>2}  {'stack':28s} state")
for k in range(1, 16):
    kind, new = legal_move(running_list[:k - 1], stacks[k - 1], running_list[k - 1], 15, 1)
    p, L = state_d1(running_list[:k], stacks[k])
    L_text = "(" + ",".join(map(str, L)) + ")" if L else "empty"
    label = paper_label(kind, stacks[k - 1], new)
    labels.append(label)
    print(f"{k:2d} {running_list[k - 1]:4d}  {label:20s} {min(running_list[:k]):2d}  {show_stack(stacks[k]):28s} W_{p}({L_text})")
assert labels == ["new minimum, merger", "interior choice", "head exhausted", "interior choice",
                  "new minimum, merger", "interior choice", "endpoint choice", "new minimum, merger",
                  "endpoint choice", "endpoint choice", "endpoint choice", "head exhausted",
                  "new minimum", "head exhausted", "head exhausted"]
assert state_d1(running_list[:6], stacks[6]) == (4, (3, 1, 1))

# %% [markdown]
# ### 2.3  The exact one-threshold recurrence
#
# **Proposition 2.13 (one-threshold recurrence).**  W_p(L) is the number of
# 1342-avoiding completions of a legal prefix with data (p, L); by
# Proposition 2.10 it depends only on (p, L).  For L = (l)L' with l >= 1,
# display (6): W_p((l)L') = sum_{h<p} W_h((l+p-1-h)L') + E_l(p, L') +
# sum_{a,b>=1, a+b=l-1} W_p((a,b)L'), with the endpoint term (7)
# E_1(p, L') = W_p(L') and E_l(p, L') = 2 W_p((l-1)L') for l >= 2; the
# boundary (8) is W_p(empty) = [p = 0] + sum_{h<p} W_h(nz(p-1-h)), where nz
# deletes zero entries from a list, so that the term h = p-1 is W_{p-1}(empty)
# and no zero part enters L; and |Av_n(1342)| = W_n(empty), display (9).  The cell implements the recurrence
# literally and compares W_n(empty) with permuta's counts.

# %%
def nz(L):
    return tuple(a for a in L if a)


@lru_cache(maxsize=None)
def W(p, L):
    """W_p(L) by displays (6)-(8), literally."""
    L = tuple(L)
    if not L:                                                           # (8)
        return (1 if p == 0 else 0) + sum(W(h, nz((p - 1 - h,))) for h in range(p))
    l, rest = L[0], L[1:]
    total = sum(W(h, (l + p - 1 - h,) + rest) for h in range(p))       # new minima
    total += W(p, rest) if l == 1 else 2 * W(p, (l - 1,) + rest)      # (7), endpoints
    total += sum(W(p, (a, l - 1 - a) + rest) for a in range(1, l - 1)) # interior, a,b >= 1
    return total


w_counts = [W(n, ()) for n in range(9)]
print("W_n(empty) for n <= 8:", w_counts)
assert w_counts == Av([beta(1)]).enumeration(8)
print("agrees with permuta's |Av_n(1342)| for n <= 8")

# %% [markdown]
# **Example 2.14 (all one-threshold moves).**  After the sixth letter of the
# running example the state is W_4((3,1,1)), and display (6) expands it as
# W_0((6,1,1)) + W_1((5,1,1)) + W_2((4,1,1)) + W_3((3,1,1)) + 2 W_4((2,1,1))
# + W_4((1,1,1,1)): the four new minima 1, 2, 3, 4, the two endpoints 6, 8 of
# the head, and its interior letter 7.  The cell checks the identity and also
# counts the 1342-avoiding completions of the prefix directly, by exploring
# all sequences of legal moves (Proposition 2.10(c) says these are exactly the
# avoiding completions), letter by letter.

# %%
def count_legal_completions(prefix, n, d):
    """The number of permutations of [n] with the given prefix all of whose
    prefixes are legal, by depth-first search over legal moves."""
    prefix = word(prefix)
    stack = scan(prefix, n, d)[-1]

    def go(prefix, stack):
        if len(prefix) == n:
            return 1
        total = 0
        for x in range(1, n + 1):
            if x in prefix:
                continue
            move = legal_move(prefix, stack, x, n, d)
            if move is not None:
                total += go(prefix + (x,), move[1])
        return total

    return go(prefix, stack)


terms = [W(0, (6, 1, 1)), W(1, (5, 1, 1)), W(2, (4, 1, 1)), W(3, (3, 1, 1)),
         2 * W(4, (2, 1, 1)), W(4, (1, 1, 1, 1))]
print("W_4((3,1,1)) =", W(4, (3, 1, 1)), "= sum of", terms, "=", sum(terms))
assert W(4, (3, 1, 1)) == sum(terms)
direct = count_legal_completions(running_list[:6], 15, 1)
print("legal completions of 9 11 10 14 5 12, by depth-first search:", direct)
assert direct == W(4, (3, 1, 1))

# %% [markdown]
# **Example 2.15 (counting Av_5(1342) by the literal recurrence).**  Display
# (8) splits |Av_5(1342)| = W_5(empty) by the first letter into
# W_0((4)) + W_1((3)) + W_2((2)) + W_3((1)) + W_4(empty), and expanding by
# (6) and (7) reaches twenty distinct states.  The cell collects every state
# the recurrence visits from W_5(empty), lists them by rho_1 = p + |L| with
# their values, as in the paper's table, and checks the expansions of
# W_0((4)), W_1((3)), W_2((2)) and W_3((1)) displayed there.

# %%
def recurrence_children(p, L):
    """The states on the right-hand side of displays (6)-(8) for W_p(L)."""
    L = tuple(L)
    if not L:                                                           # (8)
        return [(h, nz((p - 1 - h,))) for h in range(p)]
    l, rest = L[0], L[1:]
    children = [(h, (l + p - 1 - h,) + rest) for h in range(p)]        # new minima
    children.append((p, rest) if l == 1 else (p, (l - 1,) + rest))     # (7), endpoints
    children += [(p, (a, l - 1 - a) + rest) for a in range(1, l - 1)]  # interior
    return children


def states_reached(p, L):
    """All states visited when W_p(L) is expanded literally, W_p(L) included."""
    seen, todo = set(), [(p, tuple(L))]
    while todo:
        state = todo.pop()
        if state not in seen:
            seen.add(state)
            todo.extend(recurrence_children(*state))
    return seen


reached = states_reached(5, ())
print("distinct states reached from W_5(empty):", len(reached))
for rho in range(6):
    row = sorted(state for state in reached if state[0] + sum(state[1]) == rho)
    print(f"  rho_1 = {rho}:", ", ".join(f"W_{p}({L if L else 'empty'}) = {W(p, L)}" for p, L in row))
assert len(reached) == 20
first_letter_terms = [W(0, (4,)), W(1, (3,)), W(2, (2,)), W(3, (1,)), W(4, ())]
print("first-letter terms of W_5(empty):", first_letter_terms, "sum", sum(first_letter_terms))
assert first_letter_terms == [14, 20, 23, 23, 23] and W(5, ()) == 103
assert W(0, (4,)) == 2 * W(0, (3,)) + W(0, (1, 2)) + W(0, (2, 1)) == 14
assert W(1, (3,)) == W(0, (3,)) + 2 * W(1, (2,)) + W(1, (1, 1)) == 20
assert W(2, (2,)) == W(0, (3,)) + W(1, (2,)) + 2 * W(2, (1,)) == 23
assert W(3, (1,)) == W(0, (3,)) + W(1, (2,)) + W(2, (1,)) + W(3, ()) == 23
print("|Av_5(1342)| = W_5(empty) =", W(5, ()), "; permuta:", Av([beta(1)]).enumeration(5)[5])
assert W(5, ()) == Av([beta(1)]).enumeration(5)[5] == 103

# %% [markdown]
# Try your own permutation: change the string below and rerun the cell.  For
# d = 1 the scan prints every move; an illegal move means the prefix is not
# the prefix of any 1342-avoider (Proposition 2.10(c)).

# %%
my_pi = "9 11 10 14 5 12 6 2 3 8 4 7 1 13 15"  # the paper's running example
print(my_pi, "avoids 12453:", P(my_pi).avoids(tau), "| avoids 1342:", P(my_pi).avoids(beta(1)))
scan(my_pi, len(word(my_pi)), 1, verbose=True)
