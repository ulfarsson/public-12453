/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import PermPatterns.Word
import PermPatterns.Containment
import PermPatterns.Standardize
import PermPatterns.Patterns
import PermPatterns.Sums
import PermPatterns.Decidable
import PermPatterns.Avoiders
import PermPatterns.Perm
import PermPatterns.Symmetry
import PermPatterns.FirstLetter

/-!
# `PermPatterns`: a reusable core for classical permutation patterns

This library holds the generic pattern-avoidance apparatus: words, order isomorphism,
containment and avoidance, restriction, local rank and standardization, the patterns `231`
and `ι_d = 12⋯d`, increasing subsequences and triggers, direct and skew sums, decidability
of containment, the finite sets `perms n` and `avoiders n B`, the bridge to Mathlib's
`Equiv.Perm (Fin n)`, the three symmetries of a permutation class, and the first-letter
lemma for `Av(231)`.  Nothing here mentions a particular pattern class beyond `231` and
`ι_d`; the development specific to `Av(ι_d ⊕ 231)` lives in the sibling library `Av12453`.

## Contents

* `PermPatterns.Word` : words, `IsWordOn`, `IsPermOf`, `OrderIsomorphic`, `Picks`, and the
  elementary lemmas on them (`isPermOf_iff`, `orderIsomorphic_map_add`,
  `OrderIsomorphic.reverse`).
* `PermPatterns.Containment` : `Contains`, `Avoids`, `AvoidsAll`, `restrict`.
* `PermPatterns.Standardize` : `rank`, `standardize`.
* `PermPatterns.Patterns` : `pat231`, `iota`, `IncrSubseq`, `IsTriggerAt`, `IsTrigger`.
* `PermPatterns.Sums` : `directSum`, `skewSum`.
* `PermPatterns.Decidable` : decidability of `IsPermOf`, `OrderIsomorphic`, `Contains`,
  `Avoids` and `AvoidsAll`.
* `PermPatterns.Avoiders` : `perms`, `avoiders`.
* `PermPatterns.Perm` : the bridge to `Equiv.Perm (Fin n)` — `ofPerm`, `toPerm`, `permEquiv`,
  `PermContains`, `PermAvoids`.
* `PermPatterns.Symmetry` : the reverse, the complement and the inverse, and the Wilf
  equivalences they induce.
* `PermPatterns.FirstLetter` : the first-letter lemma for `Av(231)`.

## Imports

The library is import-minimised: every module lists exactly the Mathlib modules it needs,
and no module imports the root module `Mathlib` or the tactic bundle `Mathlib.Tactic`.
Importing `PermPatterns` therefore loads `607` of Mathlib's `8312` modules (`2340` modules in
all, counting the Lean, `Std`, `Batteries` and `Aesop` layers below Mathlib) instead of the
whole of Mathlib.  The Mathlib modules used are

* `Mathlib.Data.Finset.Card`, `Mathlib.Data.Finset.Dedup`, `Mathlib.Data.Finset.Insert` —
  `Finset`, `List.toFinset` and `Finset.card`;
* `Mathlib.Data.Fintype.Perm` — `Fintype (Equiv.Perm (Fin n))`;
* `Mathlib.Data.List.GetD`, `Mathlib.Data.List.NodupEquivFin`,
  `Mathlib.Data.List.Permutation`, `Mathlib.Data.List.Sublists` — `List.getD`, the order
  embedding form of `List.Sublist`, `List.permutations` and `List.sublists`;
* `Mathlib.Tactic.FinCases`, `Mathlib.Tactic.IntervalCases` — the two Mathlib tactics used
  (`simp`, `omega` and `decide` come from Lean core).

The sibling library `Av12453` is *not* import-minimised: `Av12453.Basic` imports the root
module `Mathlib` and everything downstream of it inherits all of Mathlib.

## Translation table: the usual notation and this development's

The literature numbers values and positions from `1`; **this development numbers both from
`0`**, matching Mathlib's `Fin n` and `List.range n` and the `permuta` library.  Only the
labels differ: every notion below is a statement about the *relative order* of letters,
which the two conventions describe equally well (`PermPatterns.contains_congr_word`).

| usual | Lean |
|---|---|
| values `1, 2, …, n` | values `0, 1, …, n-1`; `IsPermOf n w` is `w.Perm (List.range n)` |
| positions `1, …, n`; the letter `π_j` | positions `0, …, n-1`; the position `j` is the
  index `j - 1`; Lean quantifies over the 0-based index directly and writes the letter `w[j]` |
| the suffix after position `j`, `π_{j+1} ⋯ π_n` | `w.drop (j + 1)` after the 0-based index `j`
  (this is `w.drop j` in terms of the 1-based `j`) |
| `ι_d = 12⋯d` | `iota d = List.range d = [0, 1, …, d-1]` |
| the pattern `231` | `pat231 = [1, 2, 0]` |
| the standardization `st(w)` | `standardize w`, the rank map, with values `0, …, k-1` |
| the restriction `w\|_X` | `restrict w X`, definitionally a `List.filter` |
| local rank `r`, the number of values `≤ x` | `rank x w + 1`; `rank x w` counts the values `< x` |

## Modelling decisions

* A **word** is a `List ℕ`.  Words with *distinct entries* carry an explicit `List.Nodup`
  hypothesis wherever it is needed.  Modelling a "finite totally ordered set `I`" by a set
  of natural numbers is no loss of generality: every finite totally ordered set is
  order-isomorphic to a finite set of naturals, and every notion below is invariant under
  order isomorphism (`PermPatterns.contains_congr_word`).
* Two words are **order-isomorphic** (`PermPatterns.OrderIsomorphic`) when they have the same
  length and the same relative order at every pair of positions.  This is the relation
  usually written `st u = st v`: a word with distinct entries is order-isomorphic to its
  standardization (`PermPatterns.orderIsomorphic_standardize`), so the two readings agree.
* A word **contains** a pattern when some subsequence (`List.Sublist`; the positions need
  not be adjacent) is order-isomorphic to the pattern.  **Avoidance** is the negation.
  Containment is invariant under order isomorphism on both sides
  (`PermPatterns.contains_congr_word`, `PermPatterns.contains_congr_pattern`), so the phrase
  "avoids `231` after standardization" can be read either as `Avoids _ pat231` or literally
  as `Avoids (standardize _) pat231`; the two are equivalent
  (`PermPatterns.avoids_standardize_iff`).
* The restriction `w\|_X` is `List.filter`.

Lists of positions are required to be `List.Pairwise (· < ·)`, which by
`List.isChain_iff_pairwise` is the same as a chain `i₁ < i₂ < ⋯`.  Letters are written
`w.getD i 0`; whenever `i < w.length` this is `w[i]` (`List.getD_eq_getElem`), and every
statement carries the corresponding range hypothesis.
-/
