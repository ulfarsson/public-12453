/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Mathlib.Data.Finset.Card
import PermPatterns.Containment

/-!
# Local rank and standardization

The *local rank* of a value in a word counts the letters strictly below it, and the
*standardization* `st(w)` replaces every letter of `w` by its rank.  A word with distinct
entries is order-isomorphic to its standardization, so containment is unaffected by it.

## Main definitions

* `PermPatterns.rank`, `PermPatterns.standardize` : the `0`-based local rank and `st(w)`.

## Main results

* `PermPatterns.card_filter_le_eq_rank_succ` : the `1`-based local rank
  `r = |{y ∈ I : y ≤ x}|` equals `rank x w + 1`.
* `PermPatterns.lt_iff_length_filter_lt` : the rank map reflects and preserves the order.
* `PermPatterns.orderIsomorphic_standardize`, `PermPatterns.standardize_nodup`,
  `PermPatterns.standardize_isPermOf`, `PermPatterns.contains_standardize_iff`,
  `PermPatterns.avoids_standardize_iff` : standardization and its invariance properties.
-/

namespace PermPatterns

open List

variable {u v w s ps : List ℕ} {τ τ' : List ℕ} {m x y : ℕ}

/-! ### Local rank and standardization -/

/--
The *local rank* of `x` in the word `x :: w`, counted `0`-based: the number of letters
strictly below `x`.  The paper's local rank is `r = |{y ∈ I : y ≤ x}|`, and since `x` itself
is counted there, `r = rank x w + 1`.
-/
def rank (x : ℕ) (w : List ℕ) : ℕ := ((x :: w).filter (· < x)).length

/-- `x` does not count towards its own rank, so the rank is computed in the tail. -/
theorem rank_eq_length_filter : rank x w = (w.filter (· < x)).length := by
  rw [rank, List.filter_cons_of_neg (by simp)]

/-- The local rank as a cardinality: for a word with distinct entries, `rank x w` is the
number of values of the underlying set `I` that are strictly below `x`, i.e. the paper's
`r - 1`. -/
theorem rank_eq_card (hnd : (x :: w).Nodup) :
    rank x w = ((x :: w).toFinset.filter (fun y => y < x)).card := by
  rw [rank, ← List.toFinset_card_of_nodup (hnd.filter _)]
  refine congrArg Finset.card (Finset.ext fun a => ?_)
  constructor
  · intro ha
    have h := List.mem_filter.mp (List.mem_toFinset.mp ha)
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr h.1, by simpa using h.2⟩
  · intro ha
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp ha
    exact List.mem_toFinset.mpr
      (List.mem_filter.mpr ⟨List.mem_toFinset.mp h1, by simpa using h2⟩)

/--
**The paper's local rank.**  For a word with distinct entries, the number of values of
`I = {x} ∪ w` that are `≤ x` — the paper's `r = |{y ∈ I : y ≤ x}|` — is `rank x w + 1`,
because `x` itself is counted on the left and not on the right.  This is the bridge between
the paper's `1`-based local rank and the `0`-based `PermPatterns.rank` used here.
-/
theorem card_filter_le_eq_rank_succ (hnd : (x :: w).Nodup) :
    ((x :: w).toFinset.filter (fun y => y ≤ x)).card = rank x w + 1 := by
  have hx : x ∉ w := (List.nodup_cons.mp hnd).1
  have hcard : ((x :: w).toFinset.filter (fun y => y ≤ x)).card
      = ((x :: w).filter (fun y => y ≤ x)).length := by
    rw [← List.toFinset_card_of_nodup (hnd.filter _), List.toFinset_filter]
    simp
  have hlow : ((x :: w).filter (fun y => y ≤ x)) = x :: w.filter (· < x) := by
    rw [List.filter_cons_of_pos (by simp)]
    congr 1
    refine List.filter_congr fun a ha => ?_
    have : a ≠ x := fun he => hx (he ▸ ha)
    simp only [decide_eq_decide]
    omega
  rw [hcard, hlow, List.length_cons, rank_eq_length_filter]

/-- The number of letters of `w` below a threshold, as a cardinality. -/
theorem length_filter_lt_eq_card (hnd : w.Nodup) (z : ℕ) :
    (w.filter (· < z)).length = (w.toFinset.filter (fun a => a < z)).card := by
  rw [← List.toFinset_card_of_nodup (hnd.filter _)]
  exact congrArg Finset.card (Finset.ext fun a => by simp)

/-- The rank map `x ↦ |{y ∈ w : y < x}|` is monotone. -/
theorem length_filter_lt_mono (hnd : w.Nodup) (hxy : x ≤ y) :
    (w.filter (· < x)).length ≤ (w.filter (· < y)).length := by
  rw [length_filter_lt_eq_card hnd, length_filter_lt_eq_card hnd]
  refine Finset.card_le_card fun a ha => ?_
  simp only [Finset.mem_filter] at ha ⊢
  exact ⟨ha.1, lt_of_lt_of_le ha.2 hxy⟩

/-- The rank map is strictly monotone at the letters of a word with distinct entries. -/
theorem length_filter_lt_strictMono (hnd : w.Nodup) (hx : x ∈ w) (hxy : x < y) :
    (w.filter (· < x)).length < (w.filter (· < y)).length := by
  rw [length_filter_lt_eq_card hnd, length_filter_lt_eq_card hnd]
  have hsub : w.toFinset.filter (fun a => a < x) ⊆ w.toFinset.filter (fun a => a < y) := by
    intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, ha.2.trans hxy⟩
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨x, ?_, ?_⟩)
  · simp [List.mem_toFinset, hx, hxy]
  · simp

/-- **The rank map reflects and preserves the order.**  For a word with distinct entries and
a letter `x` of it, `x < y` holds exactly when `x` has the smaller rank. -/
theorem lt_iff_length_filter_lt (hnd : w.Nodup) (hx : x ∈ w) :
    x < y ↔ (w.filter (· < x)).length < (w.filter (· < y)).length := by
  refine ⟨length_filter_lt_strictMono hnd hx, fun h => ?_⟩
  by_contra hxy
  exact absurd (length_filter_lt_mono hnd (Nat.le_of_not_lt hxy)) (Nat.not_le.mpr h)

/-- Every rank is smaller than the length of the word: a letter of `w` is not below
itself, so the lower block is a proper part of `w`. -/
theorem length_filter_lt_length_of_mem (hnd : w.Nodup) (hx : x ∈ w) :
    (w.filter (· < x)).length < w.length := by
  rw [length_filter_lt_eq_card hnd, ← List.toFinset_card_of_nodup hnd]
  have hsub : w.toFinset.filter (fun a => a < x) ⊆ w.toFinset := fun a ha =>
    (Finset.mem_filter.mp ha).1
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨x, ?_, ?_⟩)
  · simpa using hx
  · simp

/--
The paper's *standardization* `st(w)`: every letter is replaced by its rank, so a word with
`k` distinct letters becomes a word on the values `0, 1, …, k-1` with the same relative
order.  (The paper replaces the smallest entry by `1`; here values are `0`-based, so the
smallest entry becomes `0`.)
-/
def standardize (w : List ℕ) : List ℕ := w.map (fun x => (w.filter (· < x)).length)

@[simp] theorem length_standardize : (standardize w).length = w.length := by
  simp [standardize]

/-- The `i`-th letter of `standardize w` is the rank of the `i`-th letter of `w`. -/
theorem getElem_standardize {i : ℕ} (hi : i < (standardize w).length) :
    (standardize w)[i] = (w.filter (· < w[i]'(by simpa using hi))).length := by
  simp only [standardize, List.getElem_map]

/-- **Standardization preserves the order type**: a word with distinct entries is
order-isomorphic to its standardization.  This is the precise form of the paper's `st(w)`
and the reason "avoids `231` after standardization" may be read without `st`. -/
theorem orderIsomorphic_standardize (hnd : w.Nodup) : OrderIsomorphic w (standardize w) := by
  refine ⟨by simp, fun i j hiu hju hiv hjv => ?_⟩
  rw [getElem_standardize hiv, getElem_standardize hjv]
  exact lt_iff_length_filter_lt hnd (List.getElem_mem hiu)

/-- The standardization of a word with distinct entries again has distinct entries. -/
theorem standardize_nodup (hnd : w.Nodup) : (standardize w).Nodup :=
  (orderIsomorphic_standardize hnd).nodup hnd

/-- The standardization of a word with `n` distinct letters is a permutation of
`{0, 1, …, n-1}`. -/
theorem standardize_isPermOf (hnd : w.Nodup) : IsPermOf w.length (standardize w) := by
  refine List.perm_of_nodup_nodup_toFinset_eq (standardize_nodup hnd) List.nodup_range ?_
  refine Finset.eq_of_subset_of_card_le (fun a ha => ?_) ?_
  · simp only [List.mem_toFinset, List.mem_range, standardize, List.mem_map] at ha ⊢
    obtain ⟨z, hz, rfl⟩ := ha
    exact length_filter_lt_length_of_mem hnd hz
  · rw [List.toFinset_card_of_nodup (standardize_nodup hnd),
      List.toFinset_card_of_nodup List.nodup_range]
    simp

/-- **Containment is unaffected by standardization.**  This is the bridge from the paper's
"after standardization" to the `OrderIsomorphic`-based definition used here. -/
theorem contains_standardize_iff (hnd : w.Nodup) : Contains (standardize w) τ ↔ Contains w τ :=
  (contains_congr_word (orderIsomorphic_standardize hnd)).symm

/-- **Avoidance is unaffected by standardization.** -/
theorem avoids_standardize_iff (hnd : w.Nodup) : Avoids (standardize w) τ ↔ Avoids w τ :=
  not_congr (contains_standardize_iff hnd)

/-! ### Sanity checks -/

/-- Standardization on a concrete word: the ranks of `9, 4, 7` are `2, 0, 1`. -/
example : standardize [9, 4, 7] = [2, 0, 1] := by decide

/-- The standardization of a word with distinct entries is a permutation of `{0, …, n-1}`. -/
example : IsPermOf 3 (standardize [9, 4, 7]) := standardize_isPermOf (by decide)

end PermPatterns
