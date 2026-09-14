/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Av12453.TwoThreshold.Defs

/-!
# (A) The separation invariant of the two-threshold scan

This file proves theorem (A) of component 3b: the separation criterion of
\cref{cor:separators} (i) ⟺ (ii) at `d = 2` holds at every legal prefix.  For a legal prefix
`σ`, adjacent unread values `u < v` above the second threshold `b₂` lie in different
intervals of the interval stack if and only if some letter `z` with `u < z < v` was read
after a `2`-trigger `c < u`.

The proof is the induction of the paper along the scan (`cor:separators`, the paragraph
beginning "For (i) implies (ii)"), in the three cases of the two-threshold scan:

* **Early-band move** (`x < b₁`, the case with no `d = 1` analogue).  Neither threshold
  above `x` nor the stack changes, `x` is not a `2`-trigger of the extended prefix (nothing
  smaller was read before it), and `x < b₁ < b₂ < u`, so `x` cannot be a witness `z`
  either.  Both conditions are unchanged, and the induction hypothesis applies.
* **Last-band move** (`b₁ < x < b₂`).  Now `x` is the new `b₂`, and `E = mergeSet n τ x`
  joins the active head (or becomes the whole stack).  A pair that is new above the new
  threshold has `u ∈ E`, hence `u < b₂ n τ ≤ c` for every `2`-trigger `c` of the old
  prefix, so (ii) fails; and (i) fails since `u` and `v` both lie in the single interval
  `E ∪ I₁`, or `E`.  Every other pair lies above the old `b₂`, keeps its interval (`E` is
  disjoint from it) and keeps the letters between its members.
* **Active-interval move** (`x > b₂`, `x ∈ I₁`).  The stack is nonempty, so `b₂` is a
  `2`-trigger by \cref{lem:least-trigger-frontier} (`Layout.isTrigger_b2`), and `x` is read
  after it.  The only new pair is the pair `u < x < v` of unread neighbours of `x`; then `u`
  lies in the lower part of the split head and `v` in the upper part or in a deferred
  interval, so the two are separated, and `x` witnesses (ii) with the trigger `b₂ < u`.  All
  other pairs keep both conditions.

## Main results

* `isTrigger_two_append_singleton` : the `2`-triggers of `τ ++ [x]`.
* `sep_succ_iff` : how `Sep` changes when one more letter is read.
* `sep_invariant` : theorem (A), the statement frozen for phase 2 of component 3b
  during Phase 2.
* `sepInvariant` : the same statement packaged as `SepInvariant n`, for the `_of` variants
  of the sibling modules.
-/

namespace Av12453
namespace TwoThreshold

open OneThreshold (unread mem_unread unread_append_singleton IsWord nzI mem_nzI
  stackUnion mem_stackUnion Adjacent)

variable {n : ℕ} {σ τ : List ℕ} {x u v : ℕ}

/-! ### `2`-triggers and separations along one move -/

/-- The index of the freshly read letter is the length of the prefix before it. -/
theorem idxOf_append_last (hxτ : x ∉ τ) : (τ ++ [x]).idxOf x = τ.length := by
  rw [List.idxOf_append_of_notMem hxτ]
  simp

/--
**The `2`-triggers of `τ ++ [x]`.**  Reading one more letter creates at most one new
`2`-trigger value, namely `x` itself, and only when some earlier letter is smaller.  This is
`mem_trigVals_append_singleton` in the vocabulary of `Av12453.IsTrigger`.
-/
theorem isTrigger_two_append_singleton {y : ℕ} :
    IsTrigger (τ ++ [x]) 2 y ↔ (IsTrigger τ 2 y ∨ (y = x ∧ ∃ z ∈ τ, z < x)) := by
  constructor
  · intro h
    rcases mem_trigVals_append_singleton.mp (mem_trigVals_iff.mpr h) with h' | h'
    · exact Or.inl (mem_trigVals_iff.mp h')
    · exact Or.inr h'
  · rintro (h | h)
    · exact mem_trigVals_iff.mp
        (mem_trigVals_append_singleton.mpr (Or.inl (mem_trigVals_iff.mpr h)))
    · exact mem_trigVals_iff.mp (mem_trigVals_append_singleton.mpr (Or.inr h))

/-- `Sep` is preserved when one more letter is read. -/
theorem Sep.append_singleton (h : Sep n τ u v) : Sep n (τ ++ [x]) u v := by
  obtain ⟨c, z, htc, hz, hidx, h1, h2, h3⟩ := h
  refine ⟨c, z, isTrigger_two_append_singleton.mpr (Or.inl htc),
    List.mem_append_left _ hz, ?_, h1, h2, h3⟩
  rwa [List.idxOf_append_of_mem (mem_of_isTrigger_two htc), List.idxOf_append_of_mem hz]

/--
**Reading one more letter.**  A separation of `u < v` after `τ ++ [x]` is either already a
separation after `τ`, or is witnessed by the new letter `x` itself, which then lies strictly
between `u` and `v` and follows some `2`-trigger of `τ` below `u`.  (The new letter cannot
be the *trigger* `c` of a separation: nothing has been read after it.)
-/
theorem sep_succ_iff (hxτ : x ∉ τ) :
    Sep n (τ ++ [x]) u v ↔
      (Sep n τ u v ∨ ((∃ c, IsTrigger τ 2 c ∧ c < u) ∧ u < x ∧ x < v)) := by
  constructor
  · rintro ⟨c, z, htc, hz, hidx, hcu, huz, hzv⟩
    have hxidx : (τ ++ [x]).idxOf x = τ.length := idxOf_append_last hxτ
    have hcmem : c ∈ τ ++ [x] := mem_of_isTrigger_two htc
    have hcτ : c ∈ τ := by
      rcases List.mem_append.mp hcmem with h | h
      · exact h
      · exfalso
        have hcx : c = x := List.mem_singleton.mp h
        have hzl : (τ ++ [x]).idxOf z < (τ ++ [x]).length := List.idxOf_lt_length_of_mem hz
        simp only [List.length_append, List.length_singleton] at hzl
        rw [hcx, hxidx] at hidx
        omega
    have htcτ : IsTrigger τ 2 c := by
      rcases isTrigger_two_append_singleton.mp htc with h | ⟨rfl, -⟩
      · exact h
      · exact absurd hcτ hxτ
    by_cases hzτ : z ∈ τ
    · left
      refine ⟨c, z, htcτ, hzτ, ?_, hcu, huz, hzv⟩
      rwa [List.idxOf_append_of_mem hcτ, List.idxOf_append_of_mem hzτ] at hidx
    · right
      have hzx : z = x := by
        rcases List.mem_append.mp hz with h | h
        · exact absurd h hzτ
        · exact List.mem_singleton.mp h
      subst hzx
      exact ⟨⟨c, htcτ, hcu⟩, huz, hzv⟩
  · rintro (h | ⟨⟨c, htc, hcu⟩, hux, hxv⟩)
    · exact h.append_singleton
    · have hcτ : c ∈ τ := mem_of_isTrigger_two htc
      refine ⟨c, x, isTrigger_two_append_singleton.mpr (Or.inl htc),
        List.mem_append_right _ (by simp), ?_, hcu, hux, hxv⟩
      rw [List.idxOf_append_of_mem hcτ, idxOf_append_last hxτ]
      exact List.idxOf_lt_length_of_mem hcτ

/-! ### The induction -/

private theorem sep_invariant_aux (n : ℕ) : ∀ (σ : List ℕ), Legal n σ →
    ∀ u v : ℕ, Adjacent n σ u v → b2 n σ < u → (DiffIntervals n σ u v ↔ Sep n σ u v) := by
  intro σ
  induction σ using List.reverseRecOn with
  | nil =>
    intro _ u v hadj hu
    rw [b2_nil] at hu
    have := (mem_unread.mp hadj.1).1
    omega
  | append_singleton τ x ih =>
    intro hleg u v hadj hu
    have hτ : Legal n τ := hleg.of_append_singleton
    have hx : x ∈ unread n τ := hleg.mem_unread
    have hxτ : x ∉ τ := (mem_unread.mp hx).2
    have hlay : Layout n τ := layout_of_legal hτ
    have hun : unread n (τ ++ [x]) = (unread n τ).erase x := unread_append_singleton
    obtain ⟨huσ, hvσ, huv, hbet⟩ := hadj
    have huτ' : u ∈ (unread n τ).erase x := by rw [← hun]; exact huσ
    have hvτ' : v ∈ (unread n τ).erase x := by rw [← hun]; exact hvσ
    have huτ : u ∈ unread n τ := (Finset.mem_erase.mp huτ').2
    have hux : u ≠ x := (Finset.mem_erase.mp huτ').1
    have hvτ : v ∈ unread n τ := (Finset.mem_erase.mp hvτ').2
    have hvx : v ≠ x := (Finset.mem_erase.mp hvτ').1
    -- A pair that does not straddle `x` is an adjacent pair of the shorter prefix.
    have mkAdjτ : ¬ (u < x ∧ x < v) → Adjacent n τ u v := by
      intro hxnot
      refine ⟨huτ, hvτ, huv, ?_⟩
      intro y hy hlt
      rcases eq_or_ne y x with rfl | hyx
      · exact hxnot hlt
      · exact hbet y (by rw [hun]; exact Finset.mem_erase.mpr ⟨hyx, hy⟩) hlt
    rcases mem_B0_or_B1_or_gt_b2 hx with h0 | h1 | hgt
    · -- **Early-band move.**  Nothing changes.
      have hxb1 : x < b1 n τ := (mem_B0.mp h0).2
      have hb12 : b1 n τ < b2 n τ := b1_lt_b2 n τ
      rw [b2_succ_band0 hxb1] at hu
      obtain ⟨-, hstack⟩ := legal_succ_of_band0 hτ h0
      have hsep : Sep n (τ ++ [x]) u v ↔ Sep n τ u v := by
        rw [sep_succ_iff hxτ]
        exact ⟨fun h => h.elim id fun h' => absurd h'.2.1 (by omega), Or.inl⟩
      have hdiff : DiffIntervals n (τ ++ [x]) u v ↔ DiffIntervals n τ u v := by
        simp only [DiffIntervals, hstack]
      rw [hdiff, hsep]
      exact ih hτ u v (mkAdjτ (by omega)) hu
    · -- **Last-band move.**  `x` becomes the new `b₂` and `E` joins the head.
      obtain ⟨hxun, hb1x, hxb2⟩ := mem_B1.mp h1
      rw [b2_succ_band1 hxun hb1x hxb2] at hu
      rcases lt_trichotomy u (b2 n τ) with hub | hub | hub
      · -- The new pair: `u ∈ E`.  Neither condition holds.
        have huE : u ∈ mergeSet n τ x := mem_mergeSet.mpr ⟨huτ, hu, hub⟩
        have hnosep : ¬ Sep n (τ ++ [x]) u v := by
          rw [sep_succ_iff hxτ]
          rintro (h | ⟨⟨c, htc, hcu⟩, -, -⟩)
          · obtain ⟨c, -, htc, hcu⟩ := h.mem
            have := b2_le_of_isTrigger (n := n) htc
            omega
          · have := b2_le_of_isTrigger (n := n) htc
            omega
        have hsame : ∃ I ∈ stack n (τ ++ [x]), u ∈ I ∧ v ∈ I := by
          cases hst : stack n τ with
          | cons I₁ tail =>
            have hI₁mem : I₁ ∈ stack n τ := by rw [hst]; exact List.mem_cons_self
            obtain ⟨-, hstack⟩ := legal_succ_of_band1_cons hτ hst h1
            refine ⟨mergeSet n τ x ∪ I₁, by rw [hstack]; exact List.mem_cons_self,
              Finset.mem_union_left _ huE, ?_⟩
            rcases lt_trichotomy v (b2 n τ) with hvb | hvb | hvb
            · exact Finset.mem_union_left _ (mem_mergeSet.mpr ⟨hvτ, by omega, hvb⟩)
            · exact absurd (hvb ▸ hvτ) (b2_not_unread n τ)
            · refine Finset.mem_union_right _ ?_
              obtain ⟨J, hJ, hvJ⟩ := hlay.exists_mem hvτ hvb
              rw [hst, List.mem_cons] at hJ
              rcases hJ with rfl | hJ
              · exact hvJ
              · exfalso
                obtain ⟨b, hb⟩ := hlay.nonempty I₁ hI₁mem
                obtain ⟨hcross, -⟩ := List.pairwise_cons.mp (hst ▸ hlay.ordered)
                have hbv : b < v := hcross J hJ b hb v hvJ
                have hbb2 : b2 n τ < b := hlay.lt_of_mem hI₁mem hb
                have hbun : b ∈ unread n τ := hlay.unread_of_mem hI₁mem hb
                exact hbet b (by rw [hun]; exact Finset.mem_erase.mpr ⟨by omega, hbun⟩)
                  ⟨by omega, hbv⟩
          | nil =>
            obtain ⟨-, hstack⟩ := legal_succ_of_band1_nil hτ hst h1
            have hvE : v ∈ mergeSet n τ x := by
              refine mem_mergeSet.mpr ⟨hvτ, by omega, ?_⟩
              rcases lt_trichotomy v (b2 n τ) with hvb | hvb | hvb
              · exact hvb
              · exact absurd (hvb ▸ hvτ) (b2_not_unread n τ)
              · obtain ⟨J, hJ, -⟩ := hlay.exists_mem hvτ hvb
                rw [hst] at hJ
                exact absurd hJ (by simp)
            exact ⟨mergeSet n τ x, by rw [hstack]; exact mem_nzI.mpr ⟨by simp, ⟨u, huE⟩⟩,
              huE, hvE⟩
        exact iff_of_false (fun hd => hd hsame) hnosep
      · exact absurd (hub ▸ huτ) (b2_not_unread n τ)
      · -- An old pair: both conditions are unchanged.
        have hihτ := ih hτ u v (mkAdjτ (by omega)) hub
        have huE : u ∉ mergeSet n τ x := by
          rw [mem_mergeSet]; rintro ⟨-, -, h⟩; omega
        have hvE : v ∉ mergeSet n τ x := by
          rw [mem_mergeSet]; rintro ⟨-, -, h⟩; omega
        have hsep : Sep n (τ ++ [x]) u v ↔ Sep n τ u v := by
          rw [sep_succ_iff hxτ]
          exact ⟨fun h => h.elim id fun h' => absurd h'.2.1 (by omega), Or.inl⟩
        have hdiff : DiffIntervals n (τ ++ [x]) u v ↔ DiffIntervals n τ u v := by
          cases hst : stack n τ with
          | cons I₁ tail =>
            obtain ⟨-, hstack⟩ := legal_succ_of_band1_cons hτ hst h1
            refine not_congr ⟨?_, ?_⟩
            · rintro ⟨I, hI, hui, hvi⟩
              rw [hstack, List.mem_cons] at hI
              rcases hI with rfl | hI
              · exact ⟨I₁, by rw [hst]; exact List.mem_cons_self,
                  (Finset.mem_union.mp hui).resolve_left huE,
                  (Finset.mem_union.mp hvi).resolve_left hvE⟩
              · exact ⟨I, by rw [hst]; exact List.mem_cons_of_mem _ hI, hui, hvi⟩
            · rintro ⟨I, hI, hui, hvi⟩
              rw [hst, List.mem_cons] at hI
              rcases hI with rfl | hI
              · exact ⟨mergeSet n τ x ∪ I, by rw [hstack]; exact List.mem_cons_self,
                  Finset.mem_union_right _ hui, Finset.mem_union_right _ hvi⟩
              · exact ⟨I, by rw [hstack]; exact List.mem_cons_of_mem _ hI, hui, hvi⟩
          | nil =>
            obtain ⟨-, hstack⟩ := legal_succ_of_band1_nil hτ hst h1
            refine not_congr ⟨?_, ?_⟩
            · rintro ⟨I, hI, hui, -⟩
              rw [hstack, mem_nzI, List.mem_singleton] at hI
              exact absurd (hI.1 ▸ hui) huE
            · rintro ⟨I, hI, -, -⟩
              rw [hst] at hI
              exact absurd hI (by simp)
        rw [hdiff, hsep]
        exact hihτ
    · -- **Active-interval move.**  `x ∈ I₁` splits the head.
      rw [b2_succ_above hx hgt] at hu
      cases hst : stack n τ with
      | nil => exact absurd ((legal_succ_iff_nil hτ hst).mp hleg).2 (by omega)
      | cons I₁ tail =>
        have hI₁mem : I₁ ∈ stack n τ := by rw [hst]; exact List.mem_cons_self
        have hmem : x ∈ I₁ := ((legal_succ_iff_cons hτ hst).mp hleg).2.resolve_left (by omega)
        obtain ⟨-, hstack⟩ := legal_succ_of_active hτ hst hx hgt hmem
        obtain ⟨hcross, -⟩ := List.pairwise_cons.mp (hst ▸ hlay.ordered)
        have htrig : IsTrigger τ 2 (b2 n τ) :=
          hlay.isTrigger_b2 (by rw [hst]; exact List.cons_ne_nil _ _)
        by_cases hnew : u < x ∧ x < v
        · -- The new pair: the unread neighbours of `x`.  Both conditions hold.
          obtain ⟨hux', hxv⟩ := hnew
          have huI₁ : u ∈ I₁ := hlay.head_initial hst huτ hu hmem hux'
          have hdiff : DiffIntervals n (τ ++ [x]) u v := by
            rintro ⟨I, hI, hui, hvi⟩
            rw [hstack] at hI
            rcases List.mem_append.mp hI with hI | hI
            · rw [mem_nzI, List.mem_cons, List.mem_singleton] at hI
              rcases hI.1 with rfl | rfl
              · exact absurd (Finset.mem_filter.mp hvi).2 (by omega)
              · exact absurd (Finset.mem_filter.mp hui).2 (by omega)
            · exact absurd (hcross I hI u huI₁ u hui) (lt_irrefl u)
          have hsep : Sep n (τ ++ [x]) u v := by
            rw [sep_succ_iff hxτ]
            exact Or.inr ⟨⟨b2 n τ, htrig, hu⟩, hux', hxv⟩
          exact iff_of_true hdiff hsep
        · -- An old pair: both conditions are unchanged.
          have hihτ := ih hτ u v (mkAdjτ hnew) hu
          have hcase : x < u ∨ v < x := by
            rcases Nat.lt_or_ge x u with h | h
            · exact Or.inl h
            · refine Or.inr ?_
              rcases Nat.lt_or_ge v x with h' | h'
              · exact h'
              · exact absurd ⟨by omega, by omega⟩ hnew
          have hsep : Sep n (τ ++ [x]) u v ↔ Sep n τ u v := by
            rw [sep_succ_iff hxτ]
            exact ⟨fun h => h.elim id fun h' => absurd ⟨h'.2.1, h'.2.2⟩ hnew, Or.inl⟩
          have hdiff : DiffIntervals n (τ ++ [x]) u v ↔ DiffIntervals n τ u v := by
            refine not_congr ⟨?_, ?_⟩
            · rintro ⟨I, hI, hui, hvi⟩
              rw [hstack] at hI
              rcases List.mem_append.mp hI with hI | hI
              · rw [mem_nzI, List.mem_cons, List.mem_singleton] at hI
                have hsub : I ⊆ I₁ := by
                  rcases hI.1 with rfl | rfl <;> exact Finset.filter_subset _ _
                exact ⟨I₁, hI₁mem, hsub hui, hsub hvi⟩
              · exact ⟨I, by rw [hst]; exact List.mem_cons_of_mem _ hI, hui, hvi⟩
            · rintro ⟨I, hI, hui, hvi⟩
              rw [hst, List.mem_cons] at hI
              rcases hI with rfl | hI
              · rcases hcase with h | h
                · refine ⟨I.filter (fun y => x < y), ?_, Finset.mem_filter.mpr ⟨hui, h⟩,
                    Finset.mem_filter.mpr ⟨hvi, by omega⟩⟩
                  rw [hstack]
                  exact List.mem_append_left _
                    (mem_nzI.mpr ⟨by simp, ⟨u, Finset.mem_filter.mpr ⟨hui, h⟩⟩⟩)
                · refine ⟨I.filter (· < x), ?_, Finset.mem_filter.mpr ⟨hui, by omega⟩,
                    Finset.mem_filter.mpr ⟨hvi, h⟩⟩
                  rw [hstack]
                  exact List.mem_append_left _
                    (mem_nzI.mpr ⟨by simp, ⟨u, Finset.mem_filter.mpr ⟨hui, by omega⟩⟩⟩)
              · exact ⟨I, by rw [hstack]; exact List.mem_append_right _ hI, hui, hvi⟩
          rw [hdiff, hsep]
          exact hihτ

/--
**(A) The separation invariant** (\cref{cor:separators} (i) ⟺ (ii) at `d = 2`).  For a legal
prefix and adjacent unread values `u < v` above the second threshold `b₂`, `u` and `v` lie in
different intervals of the stack if and only if some letter between them was read after a
`2`-trigger below `u`.

This is verbatim the statement frozen for the three phase-2 provers of component 3b.
-/
theorem sep_invariant (hleg : Legal n σ) (hadj : Adjacent n σ u v) (hu : b2 n σ < u) :
    DiffIntervals n σ u v ↔ Sep n σ u v :=
  sep_invariant_aux n σ hleg u v hadj hu

/-- Theorem (A) packaged as the hypothesis `SepInvariant n` of `TwoThreshold/Defs.lean`, so
that the `_of` variants of the sibling modules can be discharged with it. -/
theorem sepInvariant (n : ℕ) : SepInvariant n :=
  fun hleg hadj hu => sep_invariant hleg hadj hu

/-! ### Sanity checks

`Sep`, `Adjacent` and `DiffIntervals` are decidable, so the invariant can be evaluated on the
paper's worked example \cref{ex:full-state}.  Every check below is a kernel evaluation
(`decide`), so it adds no axiom.  The running example is
`π = 9,11,10,14,5,12,6,2,3,8,4,7,1,13,15`, written `0`-based as `runningExample`; row `k` of
the paper's table is the prefix `runningExample.take k`.
-/

/-- `Sep` with both witnesses ranging over the letters actually read. -/
theorem sep_iff_bex : Sep n σ u v ↔
    ∃ c ∈ σ, ∃ z ∈ σ, IsTrigger σ 2 c ∧ σ.idxOf c < σ.idxOf z ∧ c < u ∧ u < z ∧ z < v := by
  constructor
  · rintro ⟨c, z, htc, hz, h⟩
    exact ⟨c, mem_of_isTrigger_two htc, z, hz, htc, h⟩
  · rintro ⟨c, -, z, hz, htc, h⟩
    exact ⟨c, z, htc, hz, h⟩

instance : Decidable (Sep n σ u v) := decidable_of_iff _ sep_iff_bex.symm

instance : Decidable (DiffIntervals n σ u v) :=
  decidable_of_iff (¬ ∃ I ∈ stack n σ, u ∈ I ∧ v ∈ I) Iff.rfl

-- `Decidable (Adjacent n σ u v)` is already supplied by
-- `Av12453.OneThreshold.Invariant`, which `Av12453.TwoThreshold.Defs` imports.

set_option maxRecDepth 100000 in
/-- \cref{ex:full-state}, row `4`: after `9,11,10,14` (`0`-based `8,10,9,13`) the stack is
`{12,13} | {15}`, `0`-based `{11,12} | {14}`.  The pair `13 < 15` of the paper (`0`-based
`12 < 14`) is separated, and the paper's witness is the letter `14` (`0`-based `13`), read
after the `2`-trigger `11` (`0`-based `10`). -/
example : Adjacent 15 (runningExample.take 4) 12 14 ∧
    DiffIntervals 15 (runningExample.take 4) 12 14 ∧
    Sep 15 (runningExample.take 4) 12 14 := by
  decide

set_option maxRecDepth 100000 in
/-- The same row, the pair `12 < 13` (`0`-based `11 < 12`) inside the active head: not
separated, and no letter lies strictly between them at all. -/
example : Adjacent 15 (runningExample.take 4) 11 12 ∧
    ¬ DiffIntervals 15 (runningExample.take 4) 11 12 ∧
    ¬ Sep 15 (runningExample.take 4) 11 12 := by
  decide

set_option maxRecDepth 100000 in
/-- \cref{ex:full-state}, row `7`: after `9,11,10,14,5,12,6` (`0`-based
`8,10,9,13,4,11,5`) the stack is `{7,8,13} | {15}`, `0`-based `{6,7,12} | {14}`, and
`b₂ = 6` (`0`-based `5`).  The pair `8 < 13` (`0`-based `7 < 12`) is **not** separated even
though four letters lie strictly between them: every `2`-trigger below `8` -- there is
exactly one, `b₂ = 6` itself -- was read *after* all of them.  This is the case that makes
the trigger in \cref{cor:separators}(ii) an ordering condition and not merely a value
condition. -/
example : Adjacent 15 (runningExample.take 7) 7 12 ∧
    ¬ DiffIntervals 15 (runningExample.take 7) 7 12 ∧
    ¬ Sep 15 (runningExample.take 7) 7 12 := by
  decide

set_option maxRecDepth 100000 in
/-- The same row, the pair `13 < 15` (`0`-based `12 < 14`), which straddles the two
intervals: separated, with witness the letter `14` (`0`-based `13`) read after the
`2`-trigger `11` (`0`-based `10`). -/
example : Adjacent 15 (runningExample.take 7) 12 14 ∧
    DiffIntervals 15 (runningExample.take 7) 12 14 ∧
    Sep 15 (runningExample.take 7) 12 14 := by
  decide

set_option maxRecDepth 100000 in
/-- Adjacency cannot be dropped from \cref{cor:separators}(ii): at row `7` the values `7`
and `14` lie in different intervals, but no letter between them was read after a `2`-trigger
below `7`; they are not adjacent (`12` lies between them). -/
example : ¬ Adjacent 15 (runningExample.take 7) 7 14 ∧
    DiffIntervals 15 (runningExample.take 7) 7 14 ∧
    ¬ Sep 15 (runningExample.take 7) 7 14 := by
  decide

set_option maxRecDepth 4000000 in
/-- **The invariant itself**, checked exhaustively at every prefix of the running example
\cref{ex:full-state} and at every pair of values. -/
example : ∀ k ∈ Finset.range 16, ∀ u ∈ Finset.range 15, ∀ v ∈ Finset.range 15,
    Adjacent 15 (runningExample.take k) u v → b2 15 (runningExample.take k) < u →
      (DiffIntervals 15 (runningExample.take k) u v ↔
        Sep 15 (runningExample.take k) u v) := by
  decide

set_option maxRecDepth 8000000 in
/-- The invariant, checked exhaustively over *every* legal prefix for `n = 4`: every prefix
of every permutation of `{0, 1, 2, 3}`, and every pair of values.  (`List.permutations'` is
structurally recursive and does reduce in the kernel; `List.permutations` does not.) -/
example : ∀ σ ∈ (List.range 4).permutations', ∀ k ∈ Finset.range 5,
    Legal 4 (σ.take k) → ∀ u ∈ Finset.range 4, ∀ v ∈ Finset.range 4,
      Adjacent 4 (σ.take k) u v → b2 4 (σ.take k) < u →
        (DiffIntervals 4 (σ.take k) u v ↔ Sep 4 (σ.take k) u v) := by
  decide

set_option maxRecDepth 8000000 in
/-- The same exhaustive check at `n = 5`, the first length at which `β₂ = 12453` can occur
at all, so the first length at which a prefix can be illegal for a genuine reason. -/
example : ∀ σ ∈ (List.range 5).permutations', ∀ k ∈ Finset.range 6,
    Legal 5 (σ.take k) → ∀ u ∈ Finset.range 5, ∀ v ∈ Finset.range 5,
      Adjacent 5 (σ.take k) u v → b2 5 (σ.take k) < u →
        (DiffIntervals 5 (σ.take k) u v ↔ Sep 5 (σ.take k) u v) := by
  decide

end TwoThreshold
end Av12453
