/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Av12453.TwoThreshold.Invariant

/-!
# Semantics of the two-threshold scan: deferred letters and legal complete words

This file proves theorems **(B)** and **(C)** of component 3b, the two directions of the
scan's soundness for `d = 2` (`β₂ = 12453`, `0`-based `[0, 1, 3, 4, 2]`,
`Av12453.beta_two`):

* **(B)** `deferred_no_completion` : if the next letter `x` lies in a *deferred* interval
  `I_j`, `j ≥ 2`, of the stack of a legal prefix `σ`, then **every** permutation of
  `{0, …, n-1}` extending `σ ++ [x]` contains `12453`.  So the scan loses no avoider by
  declaring such a move illegal.
* **(C)** `legal_complete_avoids` : a legal prefix avoids `12453`; in particular a legal
  word of full length is a `12453`-avoiding permutation.  So the scan admits no
  non-avoider.

Both proofs run on the separation criterion \cref{cor:separators} (i) ⟺ (ii) at `d = 2`,
which is theorem **(A)** (`Av12453.TwoThreshold.sep_invariant`, proved in
`Av12453.TwoThreshold.Invariant`).  To keep the dependence explicit — and to let this file
be compiled in parallel with, and independently of, the proof of (A) — the two arguments are
carried out from `SepInvariant n` (`Av12453.TwoThreshold.Defs`), an abbreviation for the
statement of (A); the `_of_sep` versions therefore use no unproved result and are
axiom-clean.  The frozen names `deferred_no_completion` and `legal_complete_avoids` are
obtained from them at the end of this file by discharging that hypothesis with
`sepInvariant` of `Av12453.TwoThreshold.Invariant`.  See "Discharging the hypothesis"
below.

The only difference from the one-threshold development
(`Av12453.OneThreshold.Semantics`) is that the letter `c` supplied by `Sep` is now a
`2`-trigger rather than an arbitrary read letter, so each occurrence has **five** letters
`a < c < u < z < x` instead of four: `sep_iff_explicit` unfolds `IsTrigger σ 2 c` into its
witness `a`, and `contains_beta_two_iff` is the index form of `12453`-containment.

## The two arguments

**(B)** — this is \cref{cor:separators} (ii) ⟹ (iii) at `d = 2`, run on a pair that (i)
separates.  Let `I₁` be the active head and `y = max I₁`.  Since `x` lies in a later
interval, `y < x`, so `y` has a next unread value `v ≤ x`, and `y`, `v` are adjacent.  They
lie in different intervals (`v > max I₁`, and the intervals are pairwise increasing, hence
disjoint), so the invariant produces a `2`-trigger `c` and a letter `z` with `c < y < z < v`
and `c` read before `z`; unfolding the trigger gives `a < c` read before `c`.  In any
completion of `σ ++ [x]` the value `y` is still unread, so it is read after `x`, and the
five letters `a, c, z, x, y` occur in this order with values `a < c < y < z < x`: an
occurrence of `β₂ = 12453` (the increasing pair `a, c` is the paper's increasing
`2`-subsequence ending at the trigger, and `z, x, y ∼ 231` is its projection).

**(C).**  Suppose a legal `σ` had positions `i₁ < i₂ < j < k < l` with
`σ[i₁] < σ[i₂] < σ[l] < σ[j] < σ[k]`.  Look at the prefix `τ = σ.take k`, just before
`σ[k]` is read.  Then `σ[i₁]`, `σ[i₂]`, `σ[j]` are read and `σ[k]`, `σ[l]` are unread;
`σ[i₂]` is a `2`-trigger of `τ` (witness `σ[i₁]` before it and below it), so
`b₂ τ ≤ σ[i₂] < σ[l]` by \cref{lem:least-trigger-frontier}, and `σ[l]`, `σ[k]` are unread
values above `b₂ τ`.  Legality of the move reading `σ[k]` therefore puts `σ[k]` in the
active head `I₁`.  Let `u < v` be the adjacent unread pair straddling `σ[j]`; then
`σ[l] ≤ u < σ[j] < v ≤ σ[k]`, and since `I₁` is an initial segment of the unread values
above `b₂`, both `u` and `v` lie in `I₁`.  But `σ[j]` is a letter with `u < σ[j] < v` read
after the `2`-trigger `σ[i₂] < u`, so `Sep` holds and the invariant's `(←)` direction
separates `u` from `v` — a contradiction.

## Discharging the hypothesis

The body of this module was written in phase 2 of component 3b, in parallel with the proof
of (A), and so delivers the hypothesis-parametric forms

* `deferred_no_completion_of_sep`, `legal_avoids_of_sep`, and the packaged
  `deferredHyp_of_sep`, `completeHyp_of_sep`,

all of which are proved outright from `SepInvariant n` alone.  Since
`Av12453.TwoThreshold.Invariant` now supplies

```lean
theorem sepInvariant (n : ℕ) : SepInvariant n
```

the section "Discharging the invariant" at the end of this file specialises them to the two
unconditional theorems `deferred_no_completion` and `legal_complete_avoids`, which are the
statements the counting argument and the frozen interface of component 3b use.  No
statement in the body was weakened, and none of them was changed when the hypothesis was
discharged.

## Main results

* `contains_beta_two_iff` : the index form of `12453`-containment, for `beta 2`.
* `deferred_no_completion_of_sep`, `legal_avoids_of_sep` : (B) and (C) from the invariant.
* `deferredHyp_of_sep`, `completeHyp_of_sep` : the same, packaged as `DeferredHyp` and
  `CompleteHyp` for the counting argument (D).
* **`deferred_no_completion`**, **`legal_complete_avoids`** : (B) and (C) unconditionally,
  the frozen statements of component 3b.
-/

namespace Av12453
namespace TwoThreshold

open OneThreshold (unread mem_unread IsWord Adjacent avoiders take_succ_eq
  isPermOf_of_isWord getElem_notMem_take prefix_getElem_idxOf
  exists_adjacent_above exists_adjacent_around)

variable {n : ℕ} {σ w : List ℕ} {x : ℕ}

/-! ### The index form of `12453`-containment

`Av12453.contains_12453_iff` is stated for the literal word `[0, 1, 3, 4, 2]`; this is the
same statement for `beta 2` (`Av12453.beta_two`), which is the form the interface uses. -/

/--
**Index form of `β₂`-containment.**  A word contains the paper's `12453` — `0`-based
`β₂ = [0, 1, 3, 4, 2]` (`Av12453.beta_two`) — if and only if there are positions
`i₁ < i₂ < j < k < l` with `w[i₁] < w[i₂] < w[l] < w[j] < w[k]`.  This is
`Av12453.contains_12453_iff` with `beta 2` in place of its normal form.
-/
theorem contains_beta_two_iff (w : List ℕ) :
    Contains w (beta 2) ↔
      ∃ (i₁ i₂ j k l : ℕ) (_h₁ : i₁ < w.length) (_h₂ : i₂ < w.length) (_hj : j < w.length)
        (_hk : k < w.length) (_hl : l < w.length),
        i₁ < i₂ ∧ i₂ < j ∧ j < k ∧ k < l ∧
          w[i₁] < w[i₂] ∧ w[i₂] < w[l] ∧ w[l] < w[j] ∧ w[j] < w[k] := by
  rw [beta_two]
  exact contains_12453_iff w

/-! ### (B) Deferred letters have no completion -/

/--
**(B), from the invariant.**  If `x` lies in a deferred interval of the stack of the legal
prefix `σ`, then every permutation of `{0, …, n-1}` extending `σ ++ [x]` contains `12453`.

This is \cref{cor:separators} (ii) ⟹ (iii) at `d = 2`: the occurrence exhibited is
`a, c, z, x, y` with values `a < c < y < z < x`, where `a, c` is an increasing
`2`-subsequence ending at the trigger `c` and `z, x, y ∼ 231` is its projection onto the
values above `c`.
-/
theorem deferred_no_completion_of_sep (hA : SepInvariant n) (hleg : Legal n σ)
    {I : Finset ℕ} (hI : I ∈ (stack n σ).tail) (hx : x ∈ I) {w : List ℕ}
    (hw : IsPermOf n w) (hpre : (σ ++ [x]) <+: w) : Contains w (beta 2) := by
  have hlay : Layout n σ := layout_of_legal hleg
  have hnd : σ.Nodup := hleg.nodup
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
    have hyb : b2 n σ < I₁.max' hne := hlay.lt_of_mem hI₁mem hy
    have hxu : x ∈ unread n σ := hlay.unread_of_mem hImem hx
    have hyx : I₁.max' hne < x := hcross I hI _ hy x hx
    obtain ⟨v, hadj, hvx⟩ := exists_adjacent_above hyu hxu hyx
    -- `y` and `v` are separated: `v` is above every element of the active head
    have hdiff : DiffIntervals n σ (I₁.max' hne) v := by
      rintro ⟨J, hJ, hyJ, hvJ⟩
      rw [hst, List.mem_cons] at hJ
      rcases hJ with rfl | hJt
      · have hle : v ≤ J.max' hne := Finset.le_max' J v hvJ
        have := hadj.2.2.1
        omega
      · exact absurd (hcross J hJt _ hy _ hyJ) (lt_irrefl _)
    obtain ⟨a, c, z, ha, hc, hz, hidxac, hidxcz, hac, hcy, hyz, hzv⟩ :=
      (sep_iff_explicit hnd).mp ((hA hleg hadj hyb).mp hdiff)
    -- the five positions in `w`
    have hσw : σ <+: w := (List.prefix_append σ [x]).trans hpre
    have hlenle : σ.length + 1 ≤ w.length := by
      have := hpre.length_le
      simp only [List.length_append, List.length_singleton] at this
      omega
    obtain ⟨hpa, hwa⟩ := prefix_getElem_idxOf hσw ha
    obtain ⟨hpc, hwc⟩ := prefix_getElem_idxOf hσw hc
    obtain ⟨hpz, hwz⟩ := prefix_getElem_idxOf hσw hz
    have hzσ : σ.idxOf z < σ.length := List.idxOf_lt_length_of_mem hz
    have hpx : σ.length < w.length := by omega
    have hxlen : σ.length < (σ ++ [x]).length := by simp
    have hwx : w[σ.length]'hpx = x := by
      have h1 : (σ ++ [x])[σ.length]'hxlen = w[σ.length]'hpx := hpre.getElem hxlen
      have h2 : (σ ++ [x])[σ.length]'hxlen = x := by simp
      exact h1.symm.trans h2
    -- the value `y` is unread, so a completion reads it after `x`
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
    -- the occurrence `a, c, z, x, y`
    refine (contains_beta_two_iff w).mpr ⟨σ.idxOf a, σ.idxOf c, σ.idxOf z, σ.length,
      w.idxOf (I₁.max' hne), hpa, hpc, hpz, hpx, hpy, hidxac, hidxcz, hzσ, hpygt,
      ?_, ?_, ?_, ?_⟩
    · rw [hwa, hwc]; exact hac
    · rw [hwc, hwy]; exact hcy
    · rw [hwy, hwz]; exact hyz
    · rw [hwz, hwx]; omega

/-! ### (C) Legal prefixes avoid `12453` -/

/--
**(C), from the invariant.**  Every legal prefix avoids `12453`.  (The completeness
hypothesis `σ.length = n` of the interface statement is not needed: legality alone forbids
an occurrence.)
-/
theorem legal_avoids_of_sep (hA : SepInvariant n) (hleg : Legal n σ) :
    Avoids σ (beta 2) := by
  intro hcon
  rw [contains_beta_two_iff] at hcon
  obtain ⟨i₁, i₂, j, k, l, h₁, h₂, hj, hk, hl, pos₁, pos₂, pos₃, pos₄,
    val₁, val₂, val₃, val₄⟩ := hcon
  have hnd : σ.Nodup := hleg.nodup
  -- the prefix just before the fourth letter of the occurrence is read
  have hτpre : σ.take k <+: σ := List.take_prefix k σ
  have hndτ : (σ.take k).Nodup := List.Nodup.sublist (List.take_sublist k σ) hnd
  have hτleg : Legal n (σ.take k) := Legal.prefix hτpre hleg
  have hτlay : Layout n (σ.take k) := layout_of_legal hτleg
  have hmemτ : ∀ (i : ℕ) (hi : i < σ.length), i < k → σ[i]'hi ∈ σ.take k := by
    intro i hi hik
    have hiτ : i < (σ.take k).length := by rw [List.length_take]; omega
    have h2 : (σ.take k)[i]'hiτ = σ[i]'hi := hτpre.getElem hiτ
    exact h2 ▸ List.getElem_mem hiτ
  have hunτ : ∀ (i : ℕ) (hi : i < σ.length), k ≤ i → σ[i]'hi ∈ unread n (σ.take k) := by
    intro i hi hki
    exact mem_unread.mpr ⟨hleg.isWord.2 _ (List.getElem_mem hi),
      getElem_notMem_take hnd hi hki⟩
  have hidxτ : ∀ (i : ℕ) (hi : i < σ.length), i < k → (σ.take k).idxOf (σ[i]'hi) = i := by
    intro i hi hik
    have hiτ : i < (σ.take k).length := by rw [List.length_take]; omega
    have h2 : (σ.take k)[i]'hiτ = σ[i]'hi := hτpre.getElem hiτ
    rw [← h2]
    exact List.Nodup.idxOf_getElem hndτ i hiτ
  have hAτ : σ[i₁]'h₁ ∈ σ.take k := hmemτ i₁ h₁ (by omega)
  have hBτ : σ[i₂]'h₂ ∈ σ.take k := hmemτ i₂ h₂ (by omega)
  have hZτ : σ[j]'hj ∈ σ.take k := hmemτ j hj (by omega)
  have hLun : σ[l]'hl ∈ unread n (σ.take k) := hunτ l hl (by omega)
  have hKun : σ[k]'hk ∈ unread n (σ.take k) := hunτ k hk le_rfl
  have hZnot : σ[j]'hj ∉ unread n (σ.take k) := fun h => (mem_unread.mp h).2 hZτ
  -- `σ[i₂]` is a `2`-trigger of `τ`, witnessed by the earlier smaller letter `σ[i₁]`
  have htrig : IsTrigger (σ.take k) 2 (σ[i₂]'h₂) :=
    (isTrigger_two_iff hndτ).mpr ⟨hBτ, σ[i₁]'h₁, hAτ, by
      rw [hidxτ i₁ h₁ (by omega), hidxτ i₂ h₂ (by omega)]; omega, val₁⟩
  -- \cref{lem:least-trigger-frontier}: `b₂` is at most every trigger value
  have hb2 : b2 n (σ.take k) ≤ σ[i₂]'h₂ := b2_le_of_isTrigger htrig
  -- the move reading `σ[k]` is legal, and `σ[k]` lies above `b₂`, hence in the active head
  have hsucc : Legal n (σ.take k ++ [σ[k]'hk]) := by
    have hEq : σ.take k ++ [σ[k]'hk] = σ.take (k + 1) := by
      rw [take_succ_eq hk, List.getD_eq_getElem _ _ hk]
    rw [hEq]
    exact Legal.prefix (List.take_prefix _ _) hleg
  cases hst : stack n (σ.take k) with
  | nil =>
    have := ((legal_succ_iff_nil hτleg hst).mp hsucc).2
    omega
  | cons I₁ tl =>
    have hcI₁ : σ[k]'hk ∈ I₁ :=
      (((legal_succ_iff_cons hτleg hst).mp hsucc).2).resolve_left (by omega)
    obtain ⟨u, v, hadj, hLu, huZ, hZv, hvK⟩ :=
      exists_adjacent_around hLun hKun hZnot (by omega) (by omega)
    have hb2u : b2 n (σ.take k) < u := by omega
    have huI₁ : u ∈ I₁ := hτlay.head_initial hst hadj.1 hb2u hcI₁ (by omega)
    have hvI₁ : v ∈ I₁ := by
      rcases eq_or_lt_of_le hvK with h | h
      · exact h ▸ hcI₁
      · exact hτlay.head_initial hst hadj.2.1 (by omega) hcI₁ h
    -- `σ[j]` separates `u` from `v`: it is read after the `2`-trigger `σ[i₂] < u`
    have hsep : Sep n (σ.take k) u v :=
      ⟨σ[i₂]'h₂, σ[j]'hj, htrig, hZτ, by
        rw [hidxτ i₂ h₂ (by omega), hidxτ j hj (by omega)]; omega, by omega, huZ, hZv⟩
    exact (hA hτleg hadj hb2u).mpr hsep ⟨I₁, by rw [hst]; exact List.mem_cons_self,
      huI₁, hvI₁⟩

/-! ### The packaged hypothesis forms

`DeferredHyp` and `CompleteHyp` (`Av12453.TwoThreshold.Defs`) are the forms in which the
counting argument (D) consumes (B) and (C). -/

/-- **(B) as `DeferredHyp`**, from the invariant at every `n`. -/
theorem deferredHyp_of_sep (hA : ∀ n, SepInvariant n) : DeferredHyp :=
  fun _ _ _ hleg _ hI hx _ hw hpre => deferred_no_completion_of_sep (hA _) hleg hI hx hw hpre

set_option linter.unusedVariables false in
/-- **(C) as `CompleteHyp`**, from the invariant at every `n`. -/
theorem completeHyp_of_sep (hA : ∀ n, SepInvariant n) : CompleteHyp :=
  fun _ _ hleg hlen => legal_avoids_of_sep (hA _) hleg


/-! ### Sanity checks

At a *complete* word the two theorems together say that legality and `12453`-avoidance
coincide: (C) gives `Legal → Avoids`, and (B) gives the converse, since an illegal scan
stops at a letter of a deferred interval, which by (B) forces an occurrence of `12453`.

The kernel evaluations below check that equivalence exhaustively for `n = 4` and `n = 5`
(`List.permutations` is defined by well-founded recursion and does not reduce in the
kernel, so the permutations are listed literally).  `n = 5` is the first length at which
`12453` fits: exactly one of the `120` words, `[0, 1, 3, 4, 2] = β₂` itself, is both
illegal and non-avoiding, and `119 = |Av₅(12453)|`.  The two `#eval`s afterwards push the
same check to `n = 8` by compiled evaluation; the counts they print are the paper's
\eqref{eq:first-terms} (`code/data/av12453_terms_0_300.txt`), and `#guard_msgs` fails the
build if the output changes. -/

private def permList4 : List (List ℕ) :=
  [[0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 2, 3, 1], [0, 3, 1, 2], [0, 3, 2, 1],
   [1, 0, 2, 3], [1, 0, 3, 2], [1, 2, 0, 3], [1, 2, 3, 0], [1, 3, 0, 2], [1, 3, 2, 0],
   [2, 0, 1, 3], [2, 0, 3, 1], [2, 1, 0, 3], [2, 1, 3, 0], [2, 3, 0, 1], [2, 3, 1, 0],
   [3, 0, 1, 2], [3, 0, 2, 1], [3, 1, 0, 2], [3, 1, 2, 0], [3, 2, 0, 1], [3, 2, 1, 0]]

set_option maxRecDepth 1000000 in
/-- Legality and `12453`-avoidance agree on all `24` words of length `4`.  (No word of
length `4` contains `12453`, so this says that every such word is legal.) -/
example : ∀ w ∈ permList4, (Legal 4 w ↔ Avoids w (beta 2)) := by decide

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
/-- Legality and `12453`-avoidance agree on all `120` words of length `5`. -/
example : ∀ w ∈ permList5, (Legal 5 w ↔ Avoids w (beta 2)) := by decide

-- Legality and `12453`-avoidance agree on *every* permutation of `{0, …, k-1}` for
-- `k ≤ 8`, i.e. (B) and (C) are jointly sharp there.  Evaluated by the compiler rather
-- than by the kernel; `#guard_msgs` fails the build if the output changes, so this is a
-- live check even though `#eval` itself proves nothing.
set_option linter.hashCommand false in
/-- info: [true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval (List.range 9).map (fun k =>
  (List.range k).permutations.all (fun w => decide (Legal k w) == decide (Avoids w (beta 2))))

-- Consequently the legal words of length `k` are counted by `|Av_k(12453)|`: the first
-- nine terms `1, 1, 2, 6, 24, 119, 694, 4581, 33286` of \eqref{eq:first-terms}.  This is
-- the semantic half of the goal `av12453_count` of component 3b, checked numerically; the
-- other half, that `H` counts the legal words, is component 3b's theorem (D).
set_option linter.hashCommand false in
/-- info: [1, 1, 2, 6, 24, 119, 694, 4581, 33286] -/
#guard_msgs in
#eval (List.range 9).map (fun k =>
  ((List.range k).permutations.filter (fun w => decide (Legal k w))).length)

/-! ### Discharging the invariant

`Av12453.TwoThreshold.Invariant` proves theorem (A) and packages it as
`sepInvariant (n : ℕ) : SepInvariant n`.  Feeding that to the two `_of_sep` theorems above
gives (B) and (C) unconditionally, under the names and with the statements frozen for
component 3b. -/

/-- **(B) Deferred letters have no completion.**  If `x` lies in a deferred interval of the
stack of the legal prefix `σ`, then every permutation of `{0, …, n-1}` extending `σ ++ [x]`
contains `12453`.  This is \cref{cor:separators} (ii) ⟹ (iii) at `d = 2`; see
`deferred_no_completion_of_sep` for the proof. -/
theorem deferred_no_completion (hleg : Legal n σ) {I : Finset ℕ} (hI : I ∈ (stack n σ).tail)
    (hx : x ∈ I) {w : List ℕ} (hw : IsPermOf n w) (hpre : (σ ++ [x]) <+: w) :
    Contains w (beta 2) :=
  deferred_no_completion_of_sep (sepInvariant n) hleg hI hx hw hpre

set_option linter.unusedVariables false in
/-- **(C) Legal complete words avoid `12453`.**  The hypothesis `σ.length = n` is part of
the frozen statement but is not used: `legal_avoids_of_sep` proves that *every* legal
prefix avoids `12453`. -/
theorem legal_complete_avoids (hleg : Legal n σ) (hlen : σ.length = n) :
    Avoids σ (beta 2) :=
  legal_avoids_of_sep (sepInvariant n) hleg

end TwoThreshold
end Av12453
