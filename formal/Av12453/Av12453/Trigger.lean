/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Av12453.Basic

/-!
# Lemma 2.1 of the paper: the trigger lemma

This file proves Lemma 2.1 of *Protected tails and polynomial-time enumeration of permutations
avoiding a direct sum of an increasing pattern and 231*:

> A permutation `π = π₁ ⋯ π_n` avoids `β_d` if and only if, for every increasing
> `d`-subsequence ending at `c = π_j`, the word `π_{j+1} ⋯ π_n |_{x : x > π_j}` avoids `231`
> after standardization.

## Rendering of the statement

Values and positions are `0`-based throughout; see the translation table at the top of
`Av12453/Basic.lean`.  In particular `β_1` is `[0, 2, 3, 1]` (the paper's `1342`), `β_2` is
`[0, 1, 3, 4, 2]` (the paper's `12453`) and `231` is `pat231 = [1, 2, 0]`.

* "Increasing `d`-subsequence ending at `π_j`" is `Av12453.IsTriggerAt w d j`: there is a list
  of positions `ps` with `IncrSubseq w d ps` and `ps.getLast? = some j`.  Because the paper's
  `d`-subsequences are nonempty this forces `d ≥ 1`; the theorem carries `1 ≤ d` explicitly.
* The letters after the trigger, `π_{j+1} ⋯ π_n` in the paper, are `w.drop (j + 1)` where `j`
  is the 0-based index of the trigger (the paper's 1-based position `j` is the index `j - 1`;
  Lean quantifies over the 0-based index directly, so the trigger letter is `w[j]`).
* `w|_{x : x > π_j}` is `Av12453.restrict _ (fun x => w.getD j 0 < x)`, and `w.getD j 0 = w[j]`
  because `j < w.length` (`IsTriggerAt.lt_length`, `List.getD_eq_getElem`).
* "avoids `231` after standardization" is `Avoids _ pat231`: containment is invariant under
  order isomorphism (`Av12453.contains_congr_word`), so standardizing changes nothing.  The
  paper's phrase is also available literally, with `Av12453.standardize` applied to the
  projected tail, in `Av12453.trigger_lemma_standardized`.

## Generality

The equivalence is proved for an arbitrary word `w : List ℕ` and every `d ≥ 1`
(`Av12453.avoids_beta_iff_forall_trigger`); no `Nodup` or permutation hypothesis is needed,
since every step only compares letters with `<`.  `Av12453.trigger_lemma` is the specialization
to a permutation of `[n]`, which is the paper's sentence verbatim.

## Main results

* `Av12453.contains_beta_of_trigger` : a `d`-trigger followed by a `231` above it produces a
  `β_d` (the paper's "conversely" half).
* `Av12453.exists_trigger_of_contains_beta` : a `β_d` produces a `d`-trigger followed by a
  `231` above it (the paper's first half).
* `Av12453.avoids_beta_iff_forall_trigger`, `Av12453.trigger_lemma` : Lemma 2.1.
* `Av12453.trigger_lemma_standardized` : Lemma 2.1 with "avoids `231` after standardization"
  read literally.
-/

namespace Av12453

open List

variable {w s ps : List ℕ}

/-! ### The two halves of Lemma 2.1 -/

/--
The paper's "conversely" half of Lemma 2.1: *an increasing `d`-subsequence followed by such a
`231` has relative order `ι_d ⊕ 231 = β_d`.*

If `π_j` is a `d`-trigger and the word `π_{j+1} ⋯ π_n |_{x : x > π_j}` contains `231`, then
`π` contains `β_d`.
-/
theorem contains_beta_of_trigger {d j : ℕ} (htrig : IsTriggerAt w d j)
    (h231 : Contains (restrict (w.drop (j + 1)) (fun x => w.getD j 0 < x)) pat231) :
    Contains w (beta d) := by
  obtain ⟨ps, hps, hlast⟩ := htrig
  obtain ⟨ps', rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  -- The increasing `d`-subsequence, as a subword of the prefix `π₁ ⋯ π_j`.
  have hposP : (ps' ++ [j]).Pairwise (· < ·) := hps.pos
  have hvalP : ((ps' ++ [j]).map (fun i => w.getD i 0)).Pairwise (· < ·) := hps.val
  have hpick : Picks w (ps' ++ [j]) ((ps' ++ [j]).map (fun i => w.getD i 0)) :=
    picks_map hps.pos hps.range
  have hlt : ∀ i ∈ ps' ++ [j], i < j + 1 := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · have := (List.pairwise_append.mp hposP).2.2 i hi j (by simp)
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
  have husub : (ps' ++ [j]).map (fun i => w.getD i 0) <+ w.take (j + 1) := (hpick.take hlt).sublist
  -- The `231`, as a subword of the tail `π_{j+1} ⋯ π_n`.
  obtain ⟨s, hs, hiso⟩ := h231
  have hsw : s <+ w.drop (j + 1) := hs.trans restrict_sublist
  have hsx : ∀ x ∈ s, w.getD j 0 < x := fun x hx => (mem_restrict.mp (hs.subset hx)).2
  have hs3 : s.length = 3 := by rw [hiso.length_eq]; rfl
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hs3
  obtain ⟨hca, hab⟩ :=
    (orderIso_triple_iff (p := a) (q := b) (r := c) (x := 1) (y := 2) (z := 0)
      (by norm_num) (by norm_num)).mp hiso
  -- Glue the two pieces: they sit in this order, and the first is below the second.
  refine ⟨(ps' ++ [j]).map (fun i => w.getD i 0) ++ [a, b, c], ?_, ?_⟩
  · have hsub := husub.append hsw
    rwa [List.take_append_drop] at hsub
  · rw [beta]
    refine OrderIso.append (orderIso_iota_iff.mpr ⟨by rw [List.length_map]; exact hps.length,
      hvalP⟩) ?_ ?_ beta_lt
    · exact (orderIso_triple_iff (p := a) (q := b) (r := c) (x := d + 1) (y := d + 2)
        (z := d) (by omega) (by omega)).mpr ⟨hca, hab⟩
    · intro x hx y hy
      have hxle : x ≤ w.getD j 0 := by
        rw [List.map_append] at hx
        rcases List.mem_append.mp hx with hx | hx
        · have hsplit := List.pairwise_append.mp (by rw [← List.map_append]; exact hvalP)
          have := hsplit.2.2 x hx (w.getD j 0) (by simp)
          omega
        · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
            or_false] at hx
          omega
      exact lt_of_le_of_lt hxle (hsx y hy)

/--
The paper's first half of Lemma 2.1: *the first `d` entries of an occurrence of `β_d` form an
increasing `d`-subsequence, and its last three entries form a `231` whose values are all
larger.*

If `π` contains `β_d` (`d ≥ 1`) then some `d`-trigger `π_j` is followed by a `231` among the
letters after position `j` that exceed `π_j`.
-/
theorem exists_trigger_of_contains_beta {d : ℕ} (hd : 1 ≤ d) (h : Contains w (beta d)) :
    ∃ j, IsTriggerAt w d j ∧
      Contains (restrict (w.drop (j + 1)) (fun x => w.getD j 0 < x)) pat231 := by
  obtain ⟨qs, b, c, e, hlen, hrange, hb, hc, he, hpos, hval⟩ := (contains_beta_iff w d).mp h
  -- `qs` is nonempty, so it ends at some position `j`; this is the trigger.
  obtain ⟨qs', j, rfl⟩ : ∃ qs' j, qs = qs' ++ [j] := by
    rcases List.eq_nil_or_concat qs with rfl | ⟨qs', j, rfl⟩
    · simp only [List.length_nil] at hlen; omega
    · exact ⟨qs', j, List.concat_eq_append⟩
  obtain ⟨hposL, hposR, hposC⟩ := List.pairwise_append.mp hpos
  obtain ⟨hvalL, hvalR, hvalC⟩ := List.pairwise_append.mp hval
  refine ⟨j, ⟨qs' ++ [j], ⟨hlen, hrange, hposL, hvalL⟩, by simp⟩, ?_⟩
  -- The last three entries of the occurrence give the `231`.
  have hjmem : j ∈ qs' ++ [j] := by simp
  have hpick : Picks w [b, c, e] ([b, c, e].map (fun i => w.getD i 0)) := by
    refine picks_map hposR ?_
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> assumption
  have hge : ∀ i ∈ ([b, c, e] : List ℕ), j + 1 ≤ i := by
    intro i hi
    have := hposC j hjmem i hi
    omega
  have hsub : [b, c, e].map (fun i => w.getD i 0) <+ w.drop (j + 1) := (hpick.drop hge).sublist
  have hfj : w.getD j 0 ∈ (qs' ++ [j]).map (fun i => w.getD i 0) := by
    exact List.mem_map_of_mem hjmem
  have hgt : ∀ x ∈ ([b, c, e] : List ℕ).map (fun i => w.getD i 0), w.getD j 0 < x := by
    intro x hx
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hvalC _ hfj _ (by simp)
    · exact hvalC _ hfj _ (by simp)
    · exact hvalC _ hfj _ (by simp)
  refine ⟨[b, c, e].map (fun i => w.getD i 0), sublist_restrict_of_forall hsub hgt, ?_⟩
  obtain ⟨heb, hbc⟩ := pairwise_triple_iff.mp hvalR
  change OrderIso [w.getD b 0, w.getD c 0, w.getD e 0] pat231
  exact (orderIso_triple_iff (p := w.getD b 0) (q := w.getD c 0) (r := w.getD e 0)
    (x := 1) (y := 2) (z := 0) (by norm_num) (by norm_num)).mpr ⟨heb, hbc⟩

/-! ### Lemma 2.1 -/

/--
**Lemma 2.1 (trigger lemma), general form.**  A word `w` avoids `β_d = ι_d ⊕ 231` (for
`d ≥ 1`) if and only if, for every increasing `d`-subsequence of `w` ending at position `j`,
the word `w_{j+1} ⋯ w_n` restricted to the values exceeding `w_j` avoids `231`.

No hypothesis on `w` beyond being a word is needed; see `Av12453.trigger_lemma` for the
paper's statement about permutations of `[n]`.
-/
theorem avoids_beta_iff_forall_trigger (w : List ℕ) {d : ℕ} (hd : 1 ≤ d) :
    Avoids w (beta d) ↔
      ∀ j : ℕ, IsTriggerAt w d j →
        Avoids (restrict (w.drop (j + 1)) (fun x => w.getD j 0 < x)) pat231 := by
  constructor
  · intro havoid j htrig h231
    exact havoid (contains_beta_of_trigger htrig h231)
  · intro htails hcon
    obtain ⟨j, htrig, h231⟩ := exists_trigger_of_contains_beta hd hcon
    exact htails j htrig h231

set_option linter.unusedVariables false in
/--
**Lemma 2.1 (trigger lemma).**  A permutation `π = π₁ ⋯ π_n` of `[n]` avoids `β_d` if and only
if, for every increasing `d`-subsequence ending at `c = π_j`, the word
`π_{j+1} ⋯ π_n |_{x : x > π_j}` avoids `231` after standardization.

The permutation hypothesis `hπ` is the paper's setting; the proof does not use it (see
`Av12453.avoids_beta_iff_forall_trigger`), and it is kept only so that the statement matches
the paper's sentence.
-/
theorem trigger_lemma {n d : ℕ} {π : List ℕ} (hπ : IsPermOf n π) (hd : 1 ≤ d) :
    Avoids π (beta d) ↔
      ∀ j : ℕ, IsTriggerAt π d j →
        Avoids (restrict (π.drop (j + 1)) (fun x => π.getD j 0 < x)) pat231 :=
  avoids_beta_iff_forall_trigger π hd

/--
**Lemma 2.1 (trigger lemma), the paper's literal form.**  The same statement as
`Av12453.trigger_lemma`, with "avoids `231` *after standardization*" taken literally: the
projected tail `π_{j+1} ⋯ π_n |_{x : x > π_j}` is standardized (`Av12453.standardize`) before
`231`-avoidance is asserted.

This is a corollary of `Av12453.trigger_lemma`.  The projected tail is a subword of the
permutation `π`, so it has distinct entries — dropping a prefix preserves `Nodup`, and so
does restriction (`Av12453.restrict_nodup`) — and standardization preserves avoidance for
such words (`Av12453.avoids_standardize_iff`).  Here the permutation hypothesis `hπ` is
genuinely used, through `Av12453.IsPermOf.nodup`.
-/
theorem trigger_lemma_standardized {n d : ℕ} {π : List ℕ} (hπ : IsPermOf n π) (hd : 1 ≤ d) :
    Avoids π (beta d) ↔
      ∀ j : ℕ, IsTriggerAt π d j →
        Avoids (standardize (restrict (π.drop (j + 1)) (fun x => π.getD j 0 < x))) pat231 := by
  rw [trigger_lemma hπ hd]
  refine forall_congr' fun j => imp_congr_right fun _ => ?_
  exact (avoids_standardize_iff
    (restrict_nodup (List.Nodup.sublist (List.drop_sublist _ _) hπ.nodup))).symm

/-- The letter `π_j` used in the restriction is genuinely the `j`-th letter of `π`: for a
`d`-trigger position `j` we have `j < π.length`, so `π.getD j 0 = π[j]`. -/
theorem getD_eq_getElem_of_trigger {d j : ℕ} (h : IsTriggerAt w d j) :
    w.getD j 0 = w[j]'h.lt_length :=
  List.getD_eq_getElem _ _ h.lt_length

/-! ### The paper's two named cases -/

/-- Lemma 2.1 for `d = 1`, i.e. for the paper's `β_1 = 1342` (`0`-based: `[0, 2, 3, 1]`):
every letter is a `1`-trigger, so `π` avoids `1342` iff for every position `j` the letters
after `j` that exceed `π_j` avoid `231`. -/
theorem trigger_lemma_one (w : List ℕ) :
    Avoids w (beta 1) ↔
      ∀ j : ℕ, j < w.length →
        Avoids (restrict (w.drop (j + 1)) (fun x => w.getD j 0 < x)) pat231 := by
  rw [avoids_beta_iff_forall_trigger w le_rfl]
  exact ⟨fun h j hj => h j (isTriggerAt_one_iff.mpr hj),
    fun h j htrig => h j (isTriggerAt_one_iff.mp htrig)⟩

/-- Lemma 2.1 for the paper's main case `d = 2`, i.e. for `β_2 = 12453` (`0`-based:
`[0, 1, 3, 4, 2]`). -/
theorem trigger_lemma_two (w : List ℕ) :
    Avoids w [0, 1, 3, 4, 2] ↔
      ∀ j : ℕ, IsTriggerAt w 2 j →
        Avoids (restrict (w.drop (j + 1)) (fun x => w.getD j 0 < x)) pat231 := by
  rw [← beta_two]
  exact avoids_beta_iff_forall_trigger w (by norm_num)

/-! ### Sanity checks against the paper's conventions -/

/-- The word `β₁ = [0, 2, 3, 1]` (the paper's `1342`) is caught by Lemma 2.1 at the trigger
`π_0 = 0`: the letters after it that exceed it are `2, 3, 1`, which form a `231`. -/
example : ¬ Avoids [0, 2, 3, 1] (beta 1) := by
  intro h
  rw [trigger_lemma_one] at h
  refine h 0 (by norm_num) ?_
  have hres : restrict (([0, 2, 3, 1] : List ℕ).drop (0 + 1))
      (fun x => ([0, 2, 3, 1] : List ℕ).getD 0 0 < x) = [2, 3, 1] := by decide
  rw [hres]
  exact (contains_231_iff _).mpr
    ⟨0, 1, 2, by simp, by simp, by simp, by omega, by omega, by decide, by decide⟩

/-- The paper's main case: `β₂ = [0, 1, 3, 4, 2]` (the paper's `12453`) is caught by
Lemma 2.1 at the `2`-trigger `π_1 = 1` (reached by the increasing subsequence at positions
`0 < 1`); the letters after it that exceed it are `3, 4, 2`, which form a `231`. -/
example : ¬ Avoids [0, 1, 3, 4, 2] [0, 1, 3, 4, 2] := by
  intro h
  rw [trigger_lemma_two] at h
  refine h 1 ⟨[0, 1], ⟨rfl, by decide, by decide, by decide⟩, by decide⟩ ?_
  have hres : restrict (([0, 1, 3, 4, 2] : List ℕ).drop (1 + 1))
      (fun x => ([0, 1, 3, 4, 2] : List ℕ).getD 1 0 < x) = [3, 4, 2] := by decide
  rw [hres]
  exact (contains_231_iff _).mpr
    ⟨0, 1, 2, by simp, by simp, by simp, by omega, by omega, by decide, by decide⟩

end Av12453
