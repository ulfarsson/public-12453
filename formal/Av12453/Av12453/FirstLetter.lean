/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Av12453.Basic

/-!
# Lemma 2.2: the first-letter lemma for `Av(231)`

This file formalizes the *first-letter lemma* of Section 2 of the paper
*Protected tails and polynomial-time enumeration of permutations avoiding a direct sum of an
increasing pattern and 231*:

> Let `I` be a finite totally ordered set of size `ℓ`, and let `x ∈ I` have local rank
> `r = |{y ∈ I : y ≤ x}|`.  A permutation of `I` beginning with `x` avoids `231` if and only
> if all values below `x` occur before all values above `x`, and the two induced subwords
> avoid `231`.  Thus reading `x` replaces an interval of size `ℓ` by intervals of sizes
> `r - 1`, `ℓ - r`, in that order, with zero parts deleted.

## Modelling decisions

Values and positions are `0`-based; see the translation table at the top of
`Av12453/Basic.lean`.  In particular `231` is `pat231 = [1, 2, 0]`, and the paper's local
rank `r = |{y ∈ I : y ≤ x}|` is `Av12453.rank x w + 1`, where `rank x w = |{y ∈ I : y < x}|`
counts the values *strictly* below `x`.  The two block sizes `r - 1` and `ℓ - r` of the
paper are therefore `rank x w` and `ℓ - 1 - rank x w`.

* "A permutation of `I` beginning with `x`" is a word `x :: w` with `List.Nodup`.  The
  `Nodup` hypothesis is the paper's "permutation of a finite totally ordered set": each
  value of `I` is used exactly once, so no entry of `w` equals `x`.  It is implicit in the
  paper's word "permutation", and it is genuinely needed: the last sanity check at the end
  of this file exhibits `x = 4`, `w = [1, 4, 0]`, where the right-hand side holds but
  `4 1 4 0` contains `231`.
* Working with a word on a finite subset of `ℕ` rather than an abstract finite totally
  ordered set `I` is no loss of generality: every notion involved is invariant under order
  isomorphism (`Av12453.contains_congr_word`), and every finite totally ordered set is
  order-isomorphic to a finite set of naturals.
* "All values below `x` occur before all values above `x`" is `BelowBeforeAbove x w` below.
  The paper's "in that order" is `belowBeforeAbove_iff_append`: the condition holds exactly
  when `w` is literally the concatenation of its lower block and its upper block.
* "The two induced subwords" are `w.filter (· < x)` and `w.filter (· > x)`; these are the
  paper's `w|_{y < x}` and `w|_{y > x}`, i.e. `Av12453.restrict w (· < x)` and
  `Av12453.restrict w (· > x)` unfolded.

## Main results

* `Av12453.avoids_231_cons_iff` : the first-letter lemma itself.
* `Av12453.belowBeforeAbove_iff_append` : the block form of the ordering condition.
* `Av12453.length_filter_of_localRank` : the cardinality statement, i.e. the two blocks
  have sizes `rank x w` and `ℓ - 1 - rank x w` (the paper's `r - 1` and `ℓ - r`).
* `Av12453.length_filter_of_localRank_paper` : the same statement in the paper's own
  variables, with `r = |{y ∈ I : y ≤ x}|` and block sizes literally `r - 1` and `ℓ - r`.
* `Av12453.filter_lt_eq_restrict`, `Av12453.filter_gt_eq_restrict` : the two blocks are the
  paper's restrictions `w|_X`.
-/

namespace Av12453

open List

variable {w : List ℕ} {x : ℕ}

/-! ### The ordering condition -/

/--
The paper's condition "all values below `x` occur before all values above `x`" for the
word `w`: whenever position `i` carries a value below `x` and position `j` carries a value
above `x`, then `i < j`.
-/
def BelowBeforeAbove (x : ℕ) (w : List ℕ) : Prop :=
  ∀ (i j : ℕ) (_hi : i < w.length) (_hj : j < w.length), w[i] < x → x < w[j] → i < j

/-- The ordering condition, phrased as a `Pairwise` condition: no letter above `x` is
followed by a letter below `x`. -/
theorem belowBeforeAbove_iff_pairwise :
    BelowBeforeAbove x w ↔ w.Pairwise (fun a b => ¬ (x < a ∧ b < x)) := by
  rw [List.pairwise_iff_getElem]
  constructor
  · rintro h i j hi hj hij ⟨h1, h2⟩
    exact absurd (h j i hj hi h2 h1) (by omega)
  · intro h i j hi hj h1 h2
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact hlt
    · exfalso
      have he : w[i] = w[j] := by simp [heq]
      omega
    · exact absurd ⟨h2, h1⟩ (h j i hj hi hgt)

/--
**The paper's "in that order".**  For a word with distinct entries not containing `x`, the
condition "all values below `x` occur before all values above `x`" says exactly that `w` is
the concatenation of its lower block and its upper block.
-/
theorem belowBeforeAbove_iff_append (hx : x ∉ w) :
    BelowBeforeAbove x w ↔ w = w.filter (· < x) ++ w.filter (· > x) := by
  rw [belowBeforeAbove_iff_pairwise]
  constructor
  · intro h
    induction w with
    | nil => simp
    | cons y t ih =>
      rw [List.pairwise_cons] at h
      obtain ⟨hy, ht⟩ := h
      have hxt : x ∉ t := fun hmem => hx (List.mem_cons_of_mem _ hmem)
      have hyx : y ≠ x := fun he => hx (he ▸ List.mem_cons_self)
      rcases lt_or_gt_of_ne hyx with hlt | hgt
      · rw [List.filter_cons_of_pos (by simpa using hlt),
          List.filter_cons_of_neg (by simpa using Nat.not_lt.mpr hlt.le)]
        simpa using ih hxt ht
      · have hnone : ∀ b ∈ t, ¬ b < x := fun b hb hbx => (hy b hb) ⟨hgt, hbx⟩
        have h1 : t.filter (· < x) = [] :=
          List.filter_eq_nil_iff.mpr fun b hb => by simpa using hnone b hb
        have h2 : t.filter (· > x) = t := by
          refine List.filter_eq_self.mpr fun b hb => ?_
          have hbx : b ≠ x := fun he => hxt (he ▸ hb)
          simp only [decide_eq_true_eq, gt_iff_lt]
          rcases lt_or_gt_of_ne hbx with hb1 | hb2
          · exact absurd hb1 (hnone b hb)
          · exact hb2
        rw [List.filter_cons_of_neg (by simpa using Nat.not_lt.mpr hgt.le),
          List.filter_cons_of_pos (by simpa using hgt), h1, h2]
        simp
  · intro h
    rw [h, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · refine List.pairwise_of_forall_mem_list fun a ha b _ => ?_
      have : a < x := by simpa using (List.mem_filter.mp ha).2
      omega
    · refine List.pairwise_of_forall_mem_list fun a _ b hb => ?_
      have : x < b := by simpa using (List.mem_filter.mp hb).2
      omega
    · intro a ha b hb
      have h1 : a < x := by simpa using (List.mem_filter.mp ha).2
      have h2 : x < b := by simpa using (List.mem_filter.mp hb).2
      omega

/-! ### Auxiliary constructions of `231` occurrences -/

/-- The two blocks of the first-letter lemma are the paper's restrictions `w|_{y < x}` and
`w|_{y > x}`, i.e. `Av12453.restrict` for the two value sets. -/
theorem filter_lt_eq_restrict : w.filter (· < x) = restrict w (· < x) := rfl

/-- The two blocks of the first-letter lemma are the paper's restrictions `w|_{y < x}` and
`w|_{y > x}`, i.e. `Av12453.restrict` for the two value sets. -/
theorem filter_gt_eq_restrict : w.filter (· > x) = restrict w (· > x) := rfl

/-- A `231` occurrence all of whose letters satisfy `p` is a `231` occurrence in the
subword selected by `p`. -/
private theorem contains_231_filter_of_triple {i j k : ℕ} (hi : i < w.length)
    (hj : j < w.length) (hk : k < w.length) (hij : i < j) (hjk : j < k)
    (h1 : w[k] < w[i]) (h2 : w[i] < w[j]) (p : ℕ → Bool) (pi : p w[i] = true)
    (pj : p w[j] = true) (pk : p w[k] = true) : Contains (w.filter p) pat231 := by
  have hsub : [w[i], w[j], w[k]] <+ w.filter p :=
    sublist_filter_of_forall (triple_sublist hi hj hk hij hjk) (by
      intro a ha; fin_cases ha <;> assumption)
  exact ⟨_, hsub, (orderIso_triple_iff (x := 1) (y := 2) (z := 0) (by norm_num)
    (by norm_num)).mpr ⟨h1, h2⟩⟩

/-! ### The first-letter lemma -/

/--
**Lemma 2.2 (first-letter lemma).**  A permutation of a finite totally ordered set
beginning with `x` — here a word `x :: w` with distinct entries — avoids `231` if and only
if all values below `x` occur before all values above `x` (`BelowBeforeAbove x w`) and the
two induced subwords `w|_{y < x}` and `w|_{y > x}` avoid `231`.
-/
theorem avoids_231_cons_iff (hnd : (x :: w).Nodup) :
    Avoids (x :: w) pat231 ↔
      BelowBeforeAbove x w ∧ Avoids (w.filter (· < x)) pat231 ∧
        Avoids (w.filter (· > x)) pat231 := by
  have hx : x ∉ w := (List.nodup_cons.mp hnd).1
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · -- If an upper value occurred before a lower value, then `x`, that upper value and
      -- that lower value would form a `231`.
      intro i j hi hj h1 h2
      by_contra hij
      have hji : j < i := by
        rcases lt_trichotomy i j with hlt | heq | hgt
        · exact absurd hlt hij
        · exfalso
          have he : w[i] = w[j] := by simp [heq]
          omega
        · exact hgt
      refine absurd ((contains_231_iff (x :: w)).mpr ⟨0, j + 1, i + 1, by simp, by simpa using hj,
        by simpa using hi, by omega, by omega, ?_, ?_⟩) h
      · simpa using h1
      · simpa using h2
    · exact h.sublist (List.filter_sublist.trans (List.sublist_cons_self x w))
    · exact h.sublist (List.filter_sublist.trans (List.sublist_cons_self x w))
  · rintro ⟨hsplit, hlo, hhi⟩ hc
    rw [contains_231_iff] at hc
    obtain ⟨i, j, k, hi, hj, hk, hij, hjk, h1, h2⟩ := hc
    rcases i with _ | i
    · -- The occurrence starts at `x`; then an upper value precedes a lower value.
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hj' : j < w.length := by simpa using hj
      have hk' : k < w.length := by simpa using hk
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h1 h2
      exact absurd (hsplit k j hk' hj' h1 h2) (by omega)
    · -- The occurrence lies entirely inside `w`.
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hi' : i < w.length := by simpa using hi
      have hj' : j < w.length := by simpa using hj
      have hk' : k < w.length := by simpa using hk
      simp only [List.getElem_cons_succ] at h1 h2
      have hij' : i < j := by omega
      have hjk' : j < k := by omega
      have hne : ∀ {a : ℕ} (ha : a < w.length), w[a] ≠ x := fun ha he =>
        hx (he ▸ List.getElem_mem ha)
      rcases lt_or_gt_of_ne (hne hi') with hlo' | hhi'
      · -- `w[i] < x`, so all three letters lie in the lower block.
        have hkx : w[k] < x := by omega
        have hjx : w[j] < x := by
          rcases lt_or_gt_of_ne (hne hj') with h' | h'
          · exact h'
          · exact absurd (hsplit k j hk' hj' hkx h') (by omega)
        exact hlo (contains_231_filter_of_triple hi' hj' hk' hij' hjk' h1 h2 (· < x)
          (by simpa using hlo') (by simpa using hjx) (by simpa using hkx))
      · -- `x < w[i]`, so all three letters lie in the upper block.
        have hjx : x < w[j] := by omega
        have hkx : x < w[k] := by
          rcases lt_or_gt_of_ne (hne hk') with h' | h'
          · exact absurd (hsplit k i hk' hi' h' hhi') (by omega)
          · exact h'
        exact hhi (contains_231_filter_of_triple hi' hj' hk' hij' hjk' h1 h2 (· > x)
          (by simpa using hhi') (by simpa using hjx) (by simpa using hkx))

/-! ### The cardinality statement -/

/--
**Cardinality corollary of the first-letter lemma.**  Among the `ℓ = |I|` entries of the
word `x :: w`, the lower block has `rank x w` letters and the upper block has
`ℓ - 1 - rank x w` letters, where `rank x w = |{y ∈ I : y < x}|` is the `0`-based local rank
(`Av12453.rank`, `Av12453.rank_eq_card`).  The paper's local rank is
`r = |{y ∈ I : y ≤ x}| = rank x w + 1`, so these are the paper's block sizes `r - 1` and
`ℓ - r`, i.e. "reading `x` replaces an interval of size `ℓ` by intervals of sizes `r - 1`,
`ℓ - r`".
-/
theorem length_filter_of_localRank (hnd : (x :: w).Nodup) {ℓ : ℕ}
    (hℓ : ℓ = (x :: w).length) :
    (w.filter (· < x)).length = rank x w ∧
      (w.filter (· > x)).length = ℓ - 1 - rank x w := by
  have hx : x ∉ w := (List.nodup_cons.mp hnd).1
  -- the `0`-based local rank is the size of the lower block
  have hrank : rank x w = (w.filter (· < x)).length := rank_eq_length_filter
  -- the two blocks exhaust `w`
  have hsplit : w.length = (w.filter (· < x)).length + (w.filter (· > x)).length := by
    have := List.length_eq_length_filter_add (l := w) (fun a => decide (a < x))
    rw [show (w.filter fun a => !decide (a < x)) = w.filter (· > x) from
      List.filter_congr fun a ha => by
        have hax : a ≠ x := fun he => hx (he ▸ ha)
        simp only [← decide_not, gt_iff_lt, decide_eq_decide]
        omega] at this
    exact this
  simp only [List.length_cons] at hℓ
  omega

/--
**Cardinality corollary, in the paper's own variables.**  If `x` has local rank
`r = |{y ∈ I : y ≤ x}|` among the `ℓ = |I|` entries of the word `x :: w`, then the lower
block has `r - 1` letters and the upper block has `ℓ - r` letters.  This is the paper's
sentence "reading `x` replaces an interval of size `ℓ` by intervals of sizes `r - 1`,
`ℓ - r`" verbatim, with `r` the paper's `1`-based local rank rather than
`Av12453.rank`; the two are related by `Av12453.card_filter_le_eq_rank_succ`.
-/
theorem length_filter_of_localRank_paper (hnd : (x :: w).Nodup) {r ℓ : ℕ}
    (hℓ : ℓ = (x :: w).length)
    (hr : r = ((x :: w).toFinset.filter (fun y => y ≤ x)).card) :
    (w.filter (· < x)).length = r - 1 ∧ (w.filter (· > x)).length = ℓ - r := by
  obtain ⟨hlo, hhi⟩ := length_filter_of_localRank hnd hℓ
  rw [hr, card_filter_le_eq_rank_succ hnd]
  omega

/-! ### Sanity checks against the paper's statement -/

/-- `2 0 1 3`: the lower values `0 1` precede the upper value `3`, and both blocks avoid
`231`; the word therefore avoids `231`. -/
example : Avoids [2, 0, 1, 3] pat231 := by
  rw [avoids_231_cons_iff (by decide)]
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj h1 h2
    simp only [List.length_cons, List.length_nil] at hi hj
    interval_cases i <;> interval_cases j <;> simp_all
  · rw [show (([0, 1, 3] : List ℕ).filter (· < 2)) = [0, 1] from by decide, Avoids,
      contains_231_iff]
    rintro ⟨i, j, k, hi, hj, hk, hij, hjk, -, -⟩
    simp only [List.length_cons, List.length_nil] at hi hj hk
    omega
  · rw [show (([0, 1, 3] : List ℕ).filter (· > 2)) = [3] from by decide, Avoids,
      contains_231_iff]
    rintro ⟨i, j, k, hi, hj, hk, hij, hjk, -, -⟩
    simp only [List.length_cons, List.length_nil] at hi hj hk
    omega

/-- `2 3 0 1`: the upper value `3` precedes the lower value `0`, so the word contains
`231` (namely `2 3 0`).  This shows the ordering condition is not vacuous. -/
example : ¬ Avoids [2, 3, 0, 1] pat231 := by
  rw [avoids_231_cons_iff (by decide)]
  rintro ⟨hsplit, -, -⟩
  exact absurd (hsplit 1 0 (by decide) (by decide) (by decide) (by decide)) (by omega)

/-- **The `Nodup` hypothesis of `avoids_231_cons_iff` is necessary.**  For `x = 4` and
`w = [1, 4, 0]` the right-hand side holds — nothing in `w` exceeds `4`, so the ordering
condition is vacuous, the upper block is empty and the lower block `[1, 0]` is too short to
contain `231` — while the word `4 1 4 0` does contain `231`, at the subword `1 4 0`.  The
repeated letter `4` belongs to neither block, so the occurrence is invisible on the right.
-/
example : Contains [4, 1, 4, 0] pat231 ∧ BelowBeforeAbove 4 [1, 4, 0] ∧
    Avoids (([1, 4, 0] : List ℕ).filter (· < 4)) pat231 ∧
    Avoids (([1, 4, 0] : List ℕ).filter (· > 4)) pat231 := by
  refine ⟨(contains_231_iff _).mpr ⟨1, 2, 3, by simp, by simp, by simp, by omega, by omega,
      by decide, by decide⟩, ?_, ?_, ?_⟩
  · intro i j hi hj h1 h2
    simp only [List.length_cons, List.length_nil] at hi hj
    interval_cases j <;> simp_all
  · rw [show (([1, 4, 0] : List ℕ).filter (· < 4)) = [1, 0] from by decide, Avoids,
      contains_231_iff]
    rintro ⟨i, j, k, hi, hj, hk, hij, hjk, -, -⟩
    simp only [List.length_cons, List.length_nil] at hi hj hk
    omega
  · rw [show (([1, 4, 0] : List ℕ).filter (· > 4)) = [] from by decide, Avoids,
      contains_231_iff]
    rintro ⟨i, j, k, hi, hj, hk, -, -, -, -⟩
    simp at hi

/-- The `0`-based local rank on a concrete word: in `2 0 3 1 4` the letter `x = 2` has
`rank x w = 2` (the values `0` and `1` lie below it), so the paper's local rank is
`r = 3`. -/
example : rank 2 [0, 3, 1, 4] = 2 := by decide

/-- The cardinality statement on a concrete word: `x = 2` has `rank = 2` in the word
`2 0 3 1 4` of length `ℓ = 5`, and the two blocks have sizes `2 = rank` and
`2 = ℓ - 1 - rank`. -/
example : (([0, 3, 1, 4] : List ℕ).filter (· < 2)).length = rank 2 [0, 3, 1, 4] ∧
    (([0, 3, 1, 4] : List ℕ).filter (· > 2)).length = 5 - 1 - rank 2 [0, 3, 1, 4] :=
  length_filter_of_localRank (w := [0, 3, 1, 4]) (x := 2) (by decide) (by decide)

/-- The cardinality statement in the paper's own variables, on a concrete word: in
`2 0 3 1 4` the letter `x = 2` has paper local rank `r = |{y : y ≤ 2}| = 3` and `ℓ = 5`, so
the two blocks have sizes `2 = r - 1` and `2 = ℓ - r`. -/
example : (([0, 3, 1, 4] : List ℕ).filter (· < 2)).length = 3 - 1 ∧
    (([0, 3, 1, 4] : List ℕ).filter (· > 2)).length = 5 - 3 :=
  length_filter_of_localRank_paper (w := [0, 3, 1, 4]) (x := 2) (by decide) (by decide)
    (by decide)

end Av12453
