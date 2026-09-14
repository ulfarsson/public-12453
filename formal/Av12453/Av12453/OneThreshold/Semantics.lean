/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Av12453.OneThreshold.Invariant

/-!
# Semantics of the one-threshold scan: deferred letters and legal complete words

This file proves theorems **(B)** and **(C)** of component 3a, the two directions of the
scan's soundness for `d = 1` (`β₁ = 1342`, `0`-based `[0, 2, 3, 1]`):

* **(B)** `deferred_no_completion` : if the next letter `x` lies in a *deferred* interval
  `I_j`, `j ≥ 2`, of the stack of a legal prefix `σ`, then **every** permutation of
  `{0, …, n-1}` extending `σ ++ [x]` contains `1342`.  So the scan loses no avoider by
  declaring such a move illegal.
* **(C)** `legal_complete_avoids` : a legal prefix avoids `1342`; in particular a legal
  word of full length is a `1342`-avoiding permutation.  So the scan admits no
  non-avoider.

Both proofs run on the separation invariant of \cref{lem:1342-separators} /
\cref{cor:separators}, which is theorem **(A)** (`Av12453.OneThreshold.sep_invariant`,
proved in `Av12453.OneThreshold.Invariant`).  To keep the dependence explicit, the two
arguments are first carried out from `SepInvariant n`, an abbreviation for the statement of
(A), and only then specialised; the `_of_sep` versions therefore use no unproved result.

## The two arguments

**(B).**  Let `I₁` be the active head and `y = max I₁`.  Since `x` lies in a later interval,
`y < x`, so `y` has a next unread value `v ≤ x`, and `y`, `v` are adjacent.  They lie in
different intervals (`v > max I₁`, and the intervals are pairwise increasing, hence
disjoint), so the invariant produces read letters `c < y < z < v` with `c` read before `z`.
In any completion of `σ ++ [x]` the value `y` is still unread, so it is read after `x`, and
the four letters `c, z, x, y` occur in this order with values `c < y < z < x`: an occurrence
of `β₁`.

**(C).**  Suppose a legal `σ` had positions `a < b < c < e` with
`σ[a] < σ[e] < σ[b] < σ[c]`.  Look at the prefix `τ = σ.take c`, just before `σ[c]` is read.
Then `σ[a]`, `σ[b]` are read and `σ[e]`, `σ[c]` are unread; the threshold is `≤ σ[a]`, so
`σ[e]` and `σ[c]` are above it, and legality of the move reading `σ[c]` puts `σ[c]` in the
active head `I₁`.  Let `u < v` be the adjacent unread pair straddling `σ[b]`; then
`σ[e] ≤ u < σ[b] < v ≤ σ[c]`, and since `I₁` is an initial segment of the unread values
above the threshold, both `u` and `v` lie in `I₁`.  But `σ[b]` is a letter with `u < σ[b] < v`
read after the smaller letter `σ[a] < u`, so the invariant's `(←)` direction separates `u`
from `v` -- a contradiction.

## Main results

* `contains_beta_one_iff` : the index form of `1342`-containment.
* `deferred_no_completion_of_sep`, `legal_avoids_of_sep` : (B) and (C) from the invariant.
* `deferred_no_completion`, `legal_complete_avoids` : (B) and (C) with the invariant
  discharged by `Av12453.OneThreshold.sep_invariant`; these are the statements frozen in
  `Av12453.OneThreshold.Defs` during Phase 2.
-/

namespace Av12453
namespace OneThreshold

variable {n : ℕ} {σ w : List ℕ} {x : ℕ}

/-! ### The index form of `1342`-containment -/

/-- Four entries are increasing iff they form a chain. -/
theorem pairwise_four_iff {a b c e : ℕ} :
    ([a, b, c, e] : List ℕ).Pairwise (· < ·) ↔ a < b ∧ b < c ∧ c < e := by
  simp; omega

/--
**Index form of `β₁`-containment.**  A word contains the paper's `1342` -- `0`-based
`β₁ = [0, 2, 3, 1]` (`Av12453.beta_one`) -- if and only if there are positions
`i < j < k < l` with `w[i] < w[l] < w[j] < w[k]`.  This is `Av12453.contains_beta_iff`
at `d = 1`, written out with explicit letters as `Av12453.contains_12453_iff` does for
`d = 2`.
-/
theorem contains_beta_one_iff (w : List ℕ) :
    Contains w (beta 1) ↔
      ∃ (i j k l : ℕ) (_hi : i < w.length) (_hj : j < w.length) (_hk : k < w.length)
        (_hl : l < w.length),
        i < j ∧ j < k ∧ k < l ∧ w[i] < w[l] ∧ w[l] < w[j] ∧ w[j] < w[k] := by
  rw [contains_beta_iff]
  constructor
  · rintro ⟨ps, j, k, l, hlen, hrange, hjr, hkr, hlr, hpos, hval⟩
    obtain ⟨i, rfl⟩ : ∃ i, ps = [i] := by
      match ps, hlen with
      | [i], _ => exact ⟨i, rfl⟩
    have hi : i < w.length := hrange i (by simp)
    have hmap : ([i] : List ℕ).map (fun a => w.getD a 0) ++
        [w.getD l 0, w.getD j 0, w.getD k 0] = [w[i], w[l], w[j], w[k]] := by
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hjr,
        List.getD_eq_getElem _ _ hkr, List.getD_eq_getElem _ _ hlr]
    rw [show ([i] ++ [j, k, l] : List ℕ) = [i, j, k, l] from rfl, pairwise_four_iff] at hpos
    rw [hmap, pairwise_four_iff] at hval
    exact ⟨i, j, k, l, hi, hjr, hkr, hlr, hpos.1, hpos.2.1, hpos.2.2, hval.1, hval.2.1,
      hval.2.2⟩
  · rintro ⟨i, j, k, l, hi, hj, hk, hl, p₁, p₂, p₃, v₁, v₂, v₃⟩
    have hmap : ([i] : List ℕ).map (fun a => w.getD a 0) ++
        [w.getD l 0, w.getD j 0, w.getD k 0] = [w[i], w[l], w[j], w[k]] := by
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj,
        List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hl]
    refine ⟨[i], j, k, l, rfl, ?_, hj, hk, hl, ?_, ?_⟩
    · intro q hq
      rw [List.mem_singleton] at hq
      exact hq ▸ hi
    · rw [show ([i] ++ [j, k, l] : List ℕ) = [i, j, k, l] from rfl, pairwise_four_iff]
      exact ⟨p₁, p₂, p₃⟩
    · rw [hmap, pairwise_four_iff]
      exact ⟨v₁, v₂, v₃⟩

/-! ### Positions in a word and in a prefix of it -/

/-- In a word with distinct entries, the letter at a position `i` does not occur in any
prefix `l.take k` with `k ≤ i`. -/
theorem getElem_notMem_take {l : List ℕ} (hnd : l.Nodup) {i k : ℕ} (hi : i < l.length)
    (hk : k ≤ i) : l[i] ∉ l.take k := by
  intro hmem
  rw [List.mem_iff_getElem] at hmem
  obtain ⟨j, hj, hje⟩ := hmem
  have hjmin : j < min k l.length := by rwa [List.length_take] at hj
  have hjk : j < k := by omega
  have hjl : j < l.length := by omega
  have h1 : (l.take k)[j]'hj = l[j]'hjl :=
    List.IsPrefix.getElem (List.take_prefix k l) hj
  rw [h1] at hje
  have hj' := List.Nodup.idxOf_getElem hnd j hjl
  have hi' := List.Nodup.idxOf_getElem hnd i hi
  rw [hje] at hj'
  omega

/-- A letter of a prefix sits at its own index inside the whole word. -/
theorem prefix_getElem_idxOf {σ w : List ℕ} (hpre : σ <+: w) {a : ℕ} (ha : a ∈ σ) :
    ∃ h : σ.idxOf a < w.length, w[σ.idxOf a]'h = a := by
  have h1 : σ.idxOf a < σ.length := List.idxOf_lt_length_of_mem ha
  have h2 : σ.idxOf a < w.length := lt_of_lt_of_le h1 hpre.length_le
  exact ⟨h2, (hpre.getElem h1).symm.trans (List.getElem_idxOf h1)⟩

/-! ### Adjacent unread pairs -/

/-- The next unread value above a given one. -/
theorem exists_adjacent_above {n : ℕ} {τ : List ℕ} {y z : ℕ} (hy : y ∈ unread n τ)
    (hz : z ∈ unread n τ) (hyz : y < z) : ∃ v, Adjacent n τ y v ∧ v ≤ z := by
  have hne : ((unread n τ).filter (fun t => y < t)).Nonempty :=
    ⟨z, Finset.mem_filter.mpr ⟨hz, hyz⟩⟩
  obtain ⟨hvu, hyv⟩ := Finset.mem_filter.mp (Finset.min'_mem _ hne)
  refine ⟨((unread n τ).filter (fun t => y < t)).min' hne, ⟨hy, hvu, hyv, ?_⟩,
    Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hz, hyz⟩)⟩
  rintro t ht ⟨h1, h2⟩
  have := Finset.min'_le ((unread n τ).filter (fun t => y < t)) t
    (Finset.mem_filter.mpr ⟨ht, h1⟩)
  omega

/-- The adjacent unread pair straddling an already-read value `b`. -/
theorem exists_adjacent_around {n : ℕ} {τ : List ℕ} {lo hi b : ℕ} (hlo : lo ∈ unread n τ)
    (hhi : hi ∈ unread n τ) (hb : b ∉ unread n τ) (h1 : lo < b) (h2 : b < hi) :
    ∃ u v, Adjacent n τ u v ∧ lo ≤ u ∧ u < b ∧ b < v ∧ v ≤ hi := by
  have hlne : ((unread n τ).filter (fun t => t < b)).Nonempty :=
    ⟨lo, Finset.mem_filter.mpr ⟨hlo, h1⟩⟩
  have hrne : ((unread n τ).filter (fun t => b < t)).Nonempty :=
    ⟨hi, Finset.mem_filter.mpr ⟨hhi, h2⟩⟩
  obtain ⟨huu, hub⟩ := Finset.mem_filter.mp (Finset.max'_mem _ hlne)
  obtain ⟨hvu, hbv⟩ := Finset.mem_filter.mp (Finset.min'_mem _ hrne)
  refine ⟨((unread n τ).filter (fun t => t < b)).max' hlne,
    ((unread n τ).filter (fun t => b < t)).min' hrne, ⟨huu, hvu, by omega, ?_⟩,
    Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hlo, h1⟩), hub, hbv,
    Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hhi, h2⟩)⟩
  rintro t ht ⟨ht1, ht2⟩
  rcases lt_trichotomy t b with h | h | h
  · have := Finset.le_max' ((unread n τ).filter (fun t => t < b)) t
      (Finset.mem_filter.mpr ⟨ht, h⟩)
    omega
  · exact hb (h ▸ ht)
  · have := Finset.min'_le ((unread n τ).filter (fun t => b < t)) t
      (Finset.mem_filter.mpr ⟨ht, h⟩)
    omega

/-! ### The separation invariant as a hypothesis -/

/--
The statement of theorem **(A)**, `Av12453.OneThreshold.sep_invariant`
(\cref{lem:1342-separators}), packaged so that the arguments of this file can be run from
it as an explicit hypothesis.  (Keeping (B) and (C) parametric in the invariant is what made
them provable in parallel with (A); it also isolates them from any later change to the proof
of (A).)
-/
def SepInvariant (n : ℕ) : Prop :=
  ∀ {σ : List ℕ} {u v : ℕ}, Legal n σ → Adjacent n σ u v → m n σ < u →
    (DiffIntervals n σ u v ↔ Sep n σ u v)

/-- Theorem (A) as proved in `Av12453.OneThreshold.Invariant`. -/
theorem sepInvariant (n : ℕ) : SepInvariant n := fun hleg hadj hu => sep_invariant hleg hadj hu

/-! ### (B) Deferred letters have no completion -/

/--
**(B), from the invariant.**  If `x` lies in a deferred interval of the stack of the legal
prefix `σ`, then every permutation of `{0, …, n-1}` extending `σ ++ [x]` contains `1342`.
-/
theorem deferred_no_completion_of_sep (hA : SepInvariant n) (hleg : Legal n σ)
    {I : Finset ℕ} (hI : I ∈ (stack n σ).tail) (hx : x ∈ I) {w : List ℕ}
    (hw : IsPermOf n w) (hpre : (σ ++ [x]) <+: w) : Contains w (beta 1) := by
  have hlay : Layout n σ := layout_of_legal hleg
  cases hst : stack n σ with
  | nil => rw [hst] at hI; simp at hI
  | cons I₁ tl =>
    rw [hst, List.tail_cons] at hI
    have hpw := hlay.ordered
    rw [hst] at hpw
    obtain ⟨hcross, -⟩ := List.pairwise_cons.mp hpw
    have hI₁mem : I₁ ∈ stack n σ := by rw [hst]; exact List.mem_cons_self
    have hImem : I ∈ stack n σ := by rw [hst]; exact List.mem_cons_of_mem _ hI
    have hne : I₁.Nonempty := hlay.nonempty I₁ hI₁mem
    -- `y` is the top of the active head
    have hy : I₁.max' hne ∈ I₁ := Finset.max'_mem _ _
    have hyu : I₁.max' hne ∈ unread n σ := hlay.unread_of_mem hI₁mem hy
    have hym : m n σ < I₁.max' hne := hlay.lt_of_mem hI₁mem hy
    have hxu : x ∈ unread n σ := hlay.unread_of_mem hImem hx
    have hyx : I₁.max' hne < x := hcross I hI _ hy x hx
    obtain ⟨v, hadj, hvx⟩ := exists_adjacent_above hyu hxu hyx
    -- `y` and `v` are separated
    have hdiff : DiffIntervals n σ (I₁.max' hne) v := by
      rintro ⟨J, hJ, hyJ, hvJ⟩
      rw [hst, List.mem_cons] at hJ
      rcases hJ with rfl | hJt
      · have hle : v ≤ J.max' hne := Finset.le_max' J v hvJ
        have := hadj.2.2.1
        omega
      · exact absurd (hcross J hJt _ hy _ hyJ) (lt_irrefl _)
    obtain ⟨c, z, hc, hz, hidx, hcy, hyz, hzv⟩ := (hA hleg hadj hym).mp hdiff
    -- the four positions in `w`
    have hσw : σ <+: w := (List.prefix_append σ [x]).trans hpre
    have hlenle : σ.length + 1 ≤ w.length := by
      have := hpre.length_le
      simp only [List.length_append, List.length_singleton] at this
      omega
    obtain ⟨hpc, hwc⟩ := prefix_getElem_idxOf hσw hc
    obtain ⟨hpz, hwz⟩ := prefix_getElem_idxOf hσw hz
    have hcσ : σ.idxOf c < σ.length := List.idxOf_lt_length_of_mem hc
    have hzσ : σ.idxOf z < σ.length := List.idxOf_lt_length_of_mem hz
    have hpx : σ.length < w.length := by omega
    have hxlen : σ.length < (σ ++ [x]).length := by simp
    have hwx : w[σ.length]'hpx = x := by
      have h1 : (σ ++ [x])[σ.length]'hxlen = w[σ.length]'hpx := hpre.getElem hxlen
      have h2 : (σ ++ [x])[σ.length]'hxlen = x := by simp
      exact h1.symm.trans h2
    have hyn : I₁.max' hne < n := (mem_unread.mp hyu).1
    have hyσ : I₁.max' hne ∉ σ := (mem_unread.mp hyu).2
    have hyw : I₁.max' hne ∈ w := hw.mem_iff.mpr (List.mem_range.mpr hyn)
    have hpy : w.idxOf (I₁.max' hne) < w.length := List.idxOf_lt_length_of_mem hyw
    have hwy : w[w.idxOf (I₁.max' hne)]'hpy = I₁.max' hne := List.getElem_idxOf hpy
    have hpygt : σ.length < w.idxOf (I₁.max' hne) := by
      by_contra hcon
      have h1 : w.idxOf (I₁.max' hne) < (σ ++ [x]).length := by
        simp only [List.length_append, List.length_singleton]; omega
      have h2 : (σ ++ [x])[w.idxOf (I₁.max' hne)]'h1 = I₁.max' hne :=
        (hpre.getElem h1).trans hwy
      have h3 : I₁.max' hne ∈ σ ++ [x] := h2 ▸ List.getElem_mem h1
      rcases List.mem_append.mp h3 with h | h
      · exact hyσ h
      · rw [List.mem_singleton] at h; omega
    -- the occurrence `c, z, x, y`
    refine (contains_beta_one_iff w).mpr ⟨σ.idxOf c, σ.idxOf z, σ.length,
      w.idxOf (I₁.max' hne), hpc, hpz, hpx, hpy, hidx, hzσ, hpygt, ?_, ?_, ?_⟩
    · rw [hwc, hwy]; exact hcy
    · rw [hwy, hwz]; exact hyz
    · rw [hwz, hwx]; omega

/-! ### (C) Legal prefixes avoid `1342` -/

/--
**(C), from the invariant.**  Every legal prefix avoids `1342`.  (The completeness
hypothesis `σ.length = n` of the interface statement is not needed: legality alone forbids
an occurrence.)
-/
theorem legal_avoids_of_sep (hA : SepInvariant n) (hleg : Legal n σ) : Avoids σ (beta 1) := by
  intro hcon
  rw [contains_beta_one_iff] at hcon
  obtain ⟨a, b, c, e, ha, hb, hc, he, hab, hbc, hce, val₁, val₂, val₃⟩ := hcon
  have hnd : σ.Nodup := hleg.isWord.1
  have hτpre : σ.take c <+: σ := List.take_prefix c σ
  have hndτ : (σ.take c).Nodup := List.Nodup.sublist (List.take_sublist c σ) hnd
  have hτleg : Legal n (σ.take c) := Legal.prefix hτpre hleg
  have hτlay : Layout n (σ.take c) := layout_of_legal hτleg
  have hτlen : (σ.take c).length = c := by rw [List.length_take]; omega
  have hmemτ : ∀ (i : ℕ) (hi : i < σ.length), i < c → σ[i]'hi ∈ σ.take c := by
    intro i hi hic
    have hiτ : i < (σ.take c).length := by omega
    have h2 : (σ.take c)[i]'hiτ = σ[i]'hi := hτpre.getElem hiτ
    exact h2 ▸ List.getElem_mem hiτ
  have hunτ : ∀ (i : ℕ) (hi : i < σ.length), c ≤ i → σ[i]'hi ∈ unread n (σ.take c) := by
    intro i hi hci
    exact mem_unread.mpr ⟨hleg.isWord.2 _ (List.getElem_mem hi),
      getElem_notMem_take hnd hi hci⟩
  have hidxτ : ∀ (i : ℕ) (hi : i < σ.length), i < c → (σ.take c).idxOf (σ[i]'hi) = i := by
    intro i hi hic
    have hiτ : i < (σ.take c).length := by omega
    have h2 : (σ.take c)[i]'hiτ = σ[i]'hi := hτpre.getElem hiτ
    rw [← h2]
    exact List.Nodup.idxOf_getElem hndτ i hiτ
  have hAτ : σ[a]'ha ∈ σ.take c := hmemτ a ha (by omega)
  have hBτ : σ[b]'hb ∈ σ.take c := hmemτ b hb (by omega)
  have hEun : σ[e]'he ∈ unread n (σ.take c) := hunτ e he (by omega)
  have hCun : σ[c]'hc ∈ unread n (σ.take c) := hunτ c hc le_rfl
  have hma : m n (σ.take c) ≤ σ[a]'ha := m_le_of_mem hAτ
  have hBnot : σ[b]'hb ∉ unread n (σ.take c) := fun h => (mem_unread.mp h).2 hBτ
  have hsucc : Legal n (σ.take c ++ [σ[c]'hc]) := by
    have hEq : σ.take c ++ [σ[c]'hc] = σ.take (c + 1) := by
      rw [take_succ_eq hc, List.getD_eq_getElem _ _ hc]
    rw [hEq]
    exact Legal.prefix (List.take_prefix _ _) hleg
  cases hst : stack n (σ.take c) with
  | nil =>
    have := ((legal_succ_iff_nil hτleg hst).mp hsucc).2
    omega
  | cons I₁ tl =>
    have hcI₁ : σ[c]'hc ∈ I₁ :=
      (((legal_succ_iff_cons hτleg hst).mp hsucc).2).resolve_left (by omega)
    obtain ⟨u, v, hadj, hEu, hub, hbv, hvC⟩ :=
      exists_adjacent_around hEun hCun hBnot (by omega) (by omega)
    have hmu : m n (σ.take c) < u := by omega
    have huI₁ : u ∈ I₁ := hτlay.head_initial hst hadj.1 hmu hcI₁ (by omega)
    have hvI₁ : v ∈ I₁ := by
      rcases eq_or_lt_of_le hvC with h | h
      · exact h ▸ hcI₁
      · exact hτlay.head_initial hst hadj.2.1 (by omega) hcI₁ h
    have hsep : Sep n (σ.take c) u v :=
      ⟨σ[a]'ha, σ[b]'hb, hAτ, hBτ, by
        rw [hidxτ a ha (by omega), hidxτ b hb (by omega)]; omega, by omega, hub, hbv⟩
    exact (hA hτleg hadj hmu).mpr hsep ⟨I₁, by rw [hst]; exact List.mem_cons_self, huI₁, hvI₁⟩

/-! ### The two theorems with the invariant discharged -/

/--
**(B) Deferred letters have no completion.**  If `x` lies in a deferred interval of the
stack of a legal prefix `σ`, then every permutation of `{0, …, n-1}` extending `σ ++ [x]`
contains `1342`.
-/
theorem deferred_no_completion (hleg : Legal n σ) {I : Finset ℕ} (hI : I ∈ (stack n σ).tail)
    (hx : x ∈ I) {w : List ℕ} (hw : IsPermOf n w) (hpre : (σ ++ [x]) <+: w) :
    Contains w (beta 1) :=
  deferred_no_completion_of_sep (sepInvariant n) hleg hI hx hw hpre

set_option linter.unusedVariables false in
/-- **(C) Legal complete words avoid `1342`.**  (The proof needs only legality; see
`legal_avoids_of_sep`.) -/
theorem legal_complete_avoids (hleg : Legal n σ) (hlen : σ.length = n) :
    Avoids σ (beta 1) :=
  legal_avoids_of_sep (sepInvariant n) hleg

/-! ### Sanity checks

At a *complete* word the two theorems together say that legality and `1342`-avoidance
coincide: (C) gives `Legal → Avoids`, and (B) gives the converse, since an illegal scan
stops at a letter of a deferred interval, which by (B) forces an occurrence of `1342`.
The kernel evaluations below check that equivalence exhaustively for `n = 4` and `n = 5`
(`List.permutations` is defined by well-founded recursion and does not reduce in the
kernel, so the permutations are listed literally). -/

/-- The `24` permutations of `{0, 1, 2, 3}`. -/
private def permList4 : List (List ℕ) :=
  [[0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 2, 3, 1], [0, 3, 1, 2], [0, 3, 2, 1],
   [1, 0, 2, 3], [1, 0, 3, 2], [1, 2, 0, 3], [1, 2, 3, 0], [1, 3, 0, 2], [1, 3, 2, 0],
   [2, 0, 1, 3], [2, 0, 3, 1], [2, 1, 0, 3], [2, 1, 3, 0], [2, 3, 0, 1], [2, 3, 1, 0],
   [3, 0, 1, 2], [3, 0, 2, 1], [3, 1, 0, 2], [3, 1, 2, 0], [3, 2, 0, 1], [3, 2, 1, 0]]

set_option maxRecDepth 1000000 in
/-- Legality and `1342`-avoidance agree on all `24` words of length `4`. -/
example : ∀ w ∈ permList4, (Legal 4 w ↔ Avoids w (beta 1)) := by decide

/-- The `120` permutations of `{0, 1, 2, 3, 4}`. -/
private def permList5 : List (List ℕ) :=
  [[0, 1, 2, 3, 4], [0, 1, 2, 4, 3], [0, 1, 3, 2, 4], [0, 1, 3, 4, 2], [0, 1, 4, 2, 3],
   [0, 1, 4, 3, 2], [0, 2, 1, 3, 4], [0, 2, 1, 4, 3], [0, 2, 3, 1, 4], [0, 2, 3, 4, 1],
   [0, 2, 4, 1, 3], [0, 2, 4, 3, 1], [0, 3, 1, 2, 4], [0, 3, 1, 4, 2], [0, 3, 2, 1, 4],
   [0, 3, 2, 4, 1], [0, 3, 4, 1, 2], [0, 3, 4, 2, 1], [0, 4, 1, 2, 3], [0, 4, 1, 3, 2],
   [0, 4, 2, 1, 3], [0, 4, 2, 3, 1], [0, 4, 3, 1, 2], [0, 4, 3, 2, 1], [1, 0, 2, 3, 4],
   [1, 0, 2, 4, 3], [1, 0, 3, 2, 4], [1, 0, 3, 4, 2], [1, 0, 4, 2, 3], [1, 0, 4, 3, 2],
   [1, 2, 0, 3, 4], [1, 2, 0, 4, 3], [1, 2, 3, 0, 4], [1, 2, 3, 4, 0], [1, 2, 4, 0, 3],
   [1, 2, 4, 3, 0], [1, 3, 0, 2, 4], [1, 3, 0, 4, 2], [1, 3, 2, 0, 4], [1, 3, 2, 4, 0],
   [1, 3, 4, 0, 2], [1, 3, 4, 2, 0], [1, 4, 0, 2, 3], [1, 4, 0, 3, 2], [1, 4, 2, 0, 3],
   [1, 4, 2, 3, 0], [1, 4, 3, 0, 2], [1, 4, 3, 2, 0], [2, 0, 1, 3, 4], [2, 0, 1, 4, 3],
   [2, 0, 3, 1, 4], [2, 0, 3, 4, 1], [2, 0, 4, 1, 3], [2, 0, 4, 3, 1], [2, 1, 0, 3, 4],
   [2, 1, 0, 4, 3], [2, 1, 3, 0, 4], [2, 1, 3, 4, 0], [2, 1, 4, 0, 3], [2, 1, 4, 3, 0],
   [2, 3, 0, 1, 4], [2, 3, 0, 4, 1], [2, 3, 1, 0, 4], [2, 3, 1, 4, 0], [2, 3, 4, 0, 1],
   [2, 3, 4, 1, 0], [2, 4, 0, 1, 3], [2, 4, 0, 3, 1], [2, 4, 1, 0, 3], [2, 4, 1, 3, 0],
   [2, 4, 3, 0, 1], [2, 4, 3, 1, 0], [3, 0, 1, 2, 4], [3, 0, 1, 4, 2], [3, 0, 2, 1, 4],
   [3, 0, 2, 4, 1], [3, 0, 4, 1, 2], [3, 0, 4, 2, 1], [3, 1, 0, 2, 4], [3, 1, 0, 4, 2],
   [3, 1, 2, 0, 4], [3, 1, 2, 4, 0], [3, 1, 4, 0, 2], [3, 1, 4, 2, 0], [3, 2, 0, 1, 4],
   [3, 2, 0, 4, 1], [3, 2, 1, 0, 4], [3, 2, 1, 4, 0], [3, 2, 4, 0, 1], [3, 2, 4, 1, 0],
   [3, 4, 0, 1, 2], [3, 4, 0, 2, 1], [3, 4, 1, 0, 2], [3, 4, 1, 2, 0], [3, 4, 2, 0, 1],
   [3, 4, 2, 1, 0], [4, 0, 1, 2, 3], [4, 0, 1, 3, 2], [4, 0, 2, 1, 3], [4, 0, 2, 3, 1],
   [4, 0, 3, 1, 2], [4, 0, 3, 2, 1], [4, 1, 0, 2, 3], [4, 1, 0, 3, 2], [4, 1, 2, 0, 3],
   [4, 1, 2, 3, 0], [4, 1, 3, 0, 2], [4, 1, 3, 2, 0], [4, 2, 0, 1, 3], [4, 2, 0, 3, 1],
   [4, 2, 1, 0, 3], [4, 2, 1, 3, 0], [4, 2, 3, 0, 1], [4, 2, 3, 1, 0], [4, 3, 0, 1, 2],
   [4, 3, 0, 2, 1], [4, 3, 1, 0, 2], [4, 3, 1, 2, 0], [4, 3, 2, 0, 1], [4, 3, 2, 1, 0]]

set_option maxRecDepth 1000000 in
/-- Legality and `1342`-avoidance agree on all `120` words of length `5`. -/
example : ∀ w ∈ permList5, (Legal 5 w ↔ Avoids w (beta 1)) := by decide

end OneThreshold
end Av12453
