/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Av12453.OneThreshold.Defs

/-!
# (A) The separation invariant of the one-threshold scan

This file proves theorem (A) of component 3a: the separation criterion of
\cref{lem:1342-separators} (the case `d = 1` of \cref{cor:separators} (i) ⟺ (ii)) holds at
every legal prefix.  For a legal prefix `σ`, adjacent unread values `u < v` above the
threshold `m` lie in different intervals of the interval stack if and only if some letter
`z` with `u < z < v` was read after a letter `c < u`.

The proof is the induction of the paper along the scan, in the three cases of
\cref{lem:1342-separators}:

* **New minimum** (`x < m`).  A pair that is new above the new threshold has `u` in the
  merged set `E = mergeSet n τ x`, hence `u < m n τ`; then no read letter is below `u` at
  all except `x` itself, and every letter strictly between `u` and `v` was read *before*
  `x`, so no witness exists; on the other side `u` and `v` both lie in the single interval
  `E ∪ I₁` (or `E`), so they are not separated.  Every other pair lies above the old
  threshold, keeps its interval, and keeps the letters between its members.
* **Endpoint or interior choice** (`x ∈ I₁`).  The only new pair is the pair `u < x < v` of
  unread neighbours of `x`; then `u` lies in the lower part of the split head, `v` in the
  upper part or in a deferred interval, so the two are separated, and `x` itself is the
  witness: it was read after the threshold `m n τ < u`.
* **Unchanged pairs.**  A pair with `x` outside `(u, v)` keeps both conditions, since each
  interval of the new stack is contained in an interval of the old one and conversely.

## Main results

* `sep_succ_iff` : how `Sep` changes when one more letter is read.
* `sep_invariant` : theorem (A), the statement frozen in `Defs.lean` during Phase 2.
-/

namespace Av12453
namespace OneThreshold

variable {n : ℕ} {σ τ : List ℕ} {x u v : ℕ}

/-! ### The separation predicate along one move -/

/-- The index of the freshly read letter is the length of the prefix before it. -/
theorem idxOf_append_last (hxτ : x ∉ τ) : (τ ++ [x]).idxOf x = τ.length := by
  rw [List.idxOf_append_of_notMem hxτ]
  simp

/-- `Sep` is preserved when one more letter is read. -/
theorem Sep.append_singleton (h : Sep n τ u v) : Sep n (τ ++ [x]) u v := by
  obtain ⟨c, z, hc, hz, hidx, h1, h2, h3⟩ := h
  refine ⟨c, z, List.mem_append_left _ hc, List.mem_append_left _ hz, ?_, h1, h2, h3⟩
  rwa [List.idxOf_append_of_mem hc, List.idxOf_append_of_mem hz]

/--
**Reading one more letter.**  A separation of `u < v` after `τ ++ [x]` is either already a
separation after `τ`, or is witnessed by the new letter `x` itself, which then lies strictly
between `u` and `v` and follows some earlier letter below `u`.
-/
theorem sep_succ_iff (hxτ : x ∉ τ) :
    Sep n (τ ++ [x]) u v ↔ (Sep n τ u v ∨ ((∃ c ∈ τ, c < u) ∧ u < x ∧ x < v)) := by
  constructor
  · rintro ⟨c, z, hc, hz, hidx, hcu, huz, hzv⟩
    have hxidx : (τ ++ [x]).idxOf x = τ.length := idxOf_append_last hxτ
    by_cases hzτ : z ∈ τ
    · left
      have hzlt : (τ ++ [x]).idxOf z = τ.idxOf z := List.idxOf_append_of_mem hzτ
      have hzlen : τ.idxOf z < τ.length := List.idxOf_lt_length_of_mem hzτ
      have hcτ : c ∈ τ := by
        rcases List.mem_append.mp hc with h | h
        · exact h
        · exfalso
          rw [List.mem_singleton.mp h, hxidx, hzlt] at hidx
          omega
      rw [List.idxOf_append_of_mem hcτ, hzlt] at hidx
      exact ⟨c, z, hcτ, hzτ, hidx, hcu, huz, hzv⟩
    · right
      have hzx : z = x := by
        rcases List.mem_append.mp hz with h | h
        · exact absurd h hzτ
        · exact List.mem_singleton.mp h
      have hcτ : c ∈ τ := by
        rcases List.mem_append.mp hc with h | h
        · exact h
        · have hcx : c = x := List.mem_singleton.mp h
          exact absurd hcx (by omega)
      exact ⟨⟨c, hcτ, hcu⟩, by omega, by omega⟩
  · rintro (h | ⟨⟨c, hcτ, hcu⟩, hux, hxv⟩)
    · exact h.append_singleton
    · refine ⟨c, x, List.mem_append_left _ hcτ, List.mem_append_right _ (by simp), ?_,
        hcu, hux, hxv⟩
      rw [List.idxOf_append_of_mem hcτ, idxOf_append_last hxτ]
      exact List.idxOf_lt_length_of_mem hcτ

/-! ### The induction -/

private theorem sep_invariant_aux (n : ℕ) : ∀ (σ : List ℕ), Legal n σ →
    ∀ u v : ℕ, Adjacent n σ u v → m n σ < u → (DiffIntervals n σ u v ↔ Sep n σ u v) := by
  intro σ
  induction σ using List.reverseRecOn with
  | nil =>
    intro _ u v hadj hu
    rw [m_nil] at hu
    exact absurd (mem_unread.mp hadj.1).1 (by omega)
  | append_singleton τ x ih =>
    intro hleg u v hadj hu
    have hτ : Legal n τ := hleg.of_append_singleton
    have hx : x ∈ unread n τ := hleg.mem_unread
    have hxτ : x ∉ τ := (mem_unread.mp hx).2
    have hw : IsWord n τ := hτ.isWord
    have hlay : Layout n τ := layout_of_legal hτ
    have hmnot : m n τ ∉ unread n τ := m_not_unread hw
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
    by_cases hlt : x < m n τ
    · -- **New minimum.**
      have hm' : m n (τ ++ [x]) = x := m_succ_newMin hlt
      rw [hm'] at hu
      rcases lt_trichotomy u (m n τ) with hum | hum | hum
      · -- The new pair: `u ∈ E`.  Neither condition holds.
        have hnosep : ¬ Sep n (τ ++ [x]) u v := by
          rw [sep_succ_iff hxτ]
          rintro (⟨c, z, hc, -, -, hcu, -, -⟩ | ⟨⟨c, hc, hcu⟩, -, -⟩) <;>
            exact absurd (m_le_of_mem (n := n) hc) (by omega)
        have hsame : ∃ I ∈ stack n (τ ++ [x]), u ∈ I ∧ v ∈ I := by
          cases hst : stack n τ with
          | cons I₁ tail =>
            have hI₁mem : I₁ ∈ stack n τ := by rw [hst]; exact List.mem_cons_self
            obtain ⟨-, hstack⟩ := legal_succ_of_newMin_cons hτ hst hx hlt
            refine ⟨mergeSet n τ x ∪ I₁, by rw [hstack]; exact List.mem_cons_self,
              Finset.mem_union_left _ (mem_mergeSet.mpr ⟨huτ, hu, hum⟩), ?_⟩
            rcases lt_trichotomy v (m n τ) with hvm | hvm | hvm
            · exact Finset.mem_union_left _ (mem_mergeSet.mpr ⟨hvτ, by omega, hvm⟩)
            · exact absurd (hvm ▸ hvτ) hmnot
            · refine Finset.mem_union_right _ ?_
              obtain ⟨J, hJ, hvJ⟩ := hlay.exists_mem hvτ hvm
              rw [hst, List.mem_cons] at hJ
              rcases hJ with rfl | hJ
              · exact hvJ
              · exfalso
                obtain ⟨b, hb⟩ := hlay.nonempty I₁ hI₁mem
                obtain ⟨hcross, -⟩ := List.pairwise_cons.mp (hst ▸ hlay.ordered)
                have hbv : b < v := hcross J hJ b hb v hvJ
                have hbm : m n τ < b := hlay.lt_of_mem hI₁mem hb
                have hbu : b ∈ unread n τ := hlay.unread_of_mem hI₁mem hb
                exact hbet b (by rw [hun]; exact Finset.mem_erase.mpr ⟨by omega, hbu⟩)
                  ⟨by omega, hbv⟩
          | nil =>
            obtain ⟨-, hstack⟩ := legal_succ_of_newMin_nil hτ hst hx hlt
            have huE : u ∈ mergeSet n τ x := mem_mergeSet.mpr ⟨huτ, hu, hum⟩
            have hvE : v ∈ mergeSet n τ x := by
              refine mem_mergeSet.mpr ⟨hvτ, by omega, ?_⟩
              rcases lt_trichotomy v (m n τ) with hvm | hvm | hvm
              · exact hvm
              · exact absurd (hvm ▸ hvτ) hmnot
              · obtain ⟨J, hJ, -⟩ := hlay.exists_mem hvτ hvm
                rw [hst] at hJ
                exact absurd hJ (by simp)
            exact ⟨mergeSet n τ x, by rw [hstack]; exact mem_nzI.mpr ⟨by simp, ⟨u, huE⟩⟩,
              huE, hvE⟩
        exact iff_of_false (fun hd => hd hsame) hnosep
      · exact absurd (hum ▸ huτ) hmnot
      · -- An old pair: both conditions are unchanged.
        have hihτ := ih hτ u v (mkAdjτ (by omega)) hum
        obtain ⟨I₀, hI₀, -⟩ := hlay.exists_mem huτ hum
        cases hst : stack n τ with
        | nil => rw [hst] at hI₀; exact absurd hI₀ (by simp)
        | cons I₁ tail =>
          obtain ⟨-, hstack⟩ := legal_succ_of_newMin_cons hτ hst hx hlt
          have hsep : Sep n (τ ++ [x]) u v ↔ Sep n τ u v := by
            rw [sep_succ_iff hxτ]
            exact ⟨fun h => h.elim id (fun h' => absurd h'.2.1 (by omega)), Or.inl⟩
          have hdiff : DiffIntervals n (τ ++ [x]) u v ↔ DiffIntervals n τ u v := by
            refine not_congr ⟨?_, ?_⟩
            · rintro ⟨I, hI, hui, hvi⟩
              rw [hstack, List.mem_cons] at hI
              rcases hI with rfl | hI
              · refine ⟨I₁, by rw [hst]; exact List.mem_cons_self, ?_, ?_⟩
                · rcases Finset.mem_union.mp hui with h | h
                  · exact absurd (mem_mergeSet.mp h).2.2 (by omega)
                  · exact h
                · rcases Finset.mem_union.mp hvi with h | h
                  · exact absurd (mem_mergeSet.mp h).2.2 (by omega)
                  · exact h
              · exact ⟨I, by rw [hst]; exact List.mem_cons_of_mem _ hI, hui, hvi⟩
            · rintro ⟨I, hI, hui, hvi⟩
              rw [hst, List.mem_cons] at hI
              rcases hI with rfl | hI
              · exact ⟨mergeSet n τ x ∪ I, by rw [hstack]; exact List.mem_cons_self,
                  Finset.mem_union_right _ hui, Finset.mem_union_right _ hvi⟩
              · exact ⟨I, by rw [hstack]; exact List.mem_cons_of_mem _ hI, hui, hvi⟩
          rw [hdiff, hsep]
          exact hihτ
    · -- **Endpoint or interior choice.**
      have hm' : m n (τ ++ [x]) = m n τ := m_succ_active (by omega)
      rw [hm'] at hu
      cases hst : stack n τ with
      | nil => exact absurd ((legal_succ_iff_nil hτ hst).mp hleg).2 hlt
      | cons I₁ tail =>
        have hI₁mem : I₁ ∈ stack n τ := by rw [hst]; exact List.mem_cons_self
        have hmem : x ∈ I₁ := ((legal_succ_iff_cons hτ hst).mp hleg).2.resolve_left hlt
        obtain ⟨-, hstack⟩ := legal_succ_of_active hτ hst hx hlt hmem
        obtain ⟨hcross, -⟩ := List.pairwise_cons.mp (hst ▸ hlay.ordered)
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
          have hne : τ ≠ [] := by
            rintro rfl
            rw [m_nil] at hlt
            exact hlt (mem_unread.mp hx).1
          have hmτ : m n τ ∈ τ := m_mem hw hne
          have hsep : Sep n (τ ++ [x]) u v := by
            refine ⟨m n τ, x, List.mem_append_left _ hmτ,
              List.mem_append_right _ (by simp), ?_, hu, hux', hxv⟩
            rw [List.idxOf_append_of_mem hmτ, idxOf_append_last hxτ]
            exact List.idxOf_lt_length_of_mem hmτ
          exact iff_of_true hdiff hsep
        · -- An old pair: both conditions are unchanged.
          have hihτ := ih hτ u v (mkAdjτ hnew) hu
          have hcase : x < u ∨ v < x := by omega
          have hsep : Sep n (τ ++ [x]) u v ↔ Sep n τ u v := by
            rw [sep_succ_iff hxτ]
            exact ⟨fun h => h.elim id (fun h' => absurd ⟨h'.2.1, h'.2.2⟩ hnew), Or.inl⟩
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
**(A) The separation invariant** (\cref{lem:1342-separators}, both directions; the case
`d = 1` of \cref{cor:separators} (i) ⟺ (ii)).  For a legal prefix and adjacent unread values
`u < v` above the threshold, `u` and `v` lie in different intervals of the stack if and only
if some letter between them was read after a smaller letter.

This is verbatim the statement frozen as a placeholder in `Defs.lean` during Phase 2.
-/
theorem sep_invariant (hleg : Legal n σ) (hadj : Adjacent n σ u v) (hu : m n σ < u) :
    DiffIntervals n σ u v ↔ Sep n σ u v :=
  sep_invariant_aux n σ hleg u v hadj hu

/-! ### Sanity checks

`Sep` and `DiffIntervals` are decidable, so the invariant can be evaluated on the paper's
worked examples.  Every check below is a kernel evaluation (`decide`), so it adds no axiom.
-/

/-- `Sep` with both witnesses ranging over the letters actually read. -/
theorem sep_iff_bex : Sep n σ u v ↔
    ∃ c ∈ σ, ∃ z ∈ σ, σ.idxOf c < σ.idxOf z ∧ c < u ∧ u < z ∧ z < v := by
  constructor
  · rintro ⟨c, z, hc, hz, h⟩; exact ⟨c, hc, z, hz, h⟩
  · rintro ⟨c, hc, z, hz, h⟩; exact ⟨c, z, hc, hz, h⟩

instance : Decidable (Sep n σ u v) := decidable_of_iff _ sep_iff_bex.symm

instance : Decidable (Adjacent n σ u v) :=
  decidable_of_iff (u ∈ unread n σ ∧ v ∈ unread n σ ∧ u < v ∧
    ∀ y ∈ unread n σ, ¬(u < y ∧ y < v)) Iff.rfl

instance : Decidable (DiffIntervals n σ u v) :=
  decidable_of_iff (¬ ∃ I ∈ stack n σ, u ∈ I ∧ v ∈ I) Iff.rfl

set_option maxRecDepth 100000 in
/-- \cref{ex:1342-scan}, row `5`: after `9,11,10,14,5` the stack is `{6,7,8,12,13} | {15}`,
which `0`-based is `{5,6,7,11,12} | {14}`.  The adjacent pair `8 < 12` of the paper (`0`-based
`7 < 11`) is not separated: the letters `9,10,11` between them were all read before any
letter below `8`. -/
example : Adjacent 15 (runningExample.take 5) 7 11 ∧
    ¬ DiffIntervals 15 (runningExample.take 5) 7 11 ∧ ¬ Sep 15 (runningExample.take 5) 7 11 := by
  decide

set_option maxRecDepth 100000 in
/-- \cref{ex:1342-scan}, row `5`, continued: `14` was read after `9 < 13`, so it separates
`13` from `15` (`0`-based: `13` separates `12` from `14`). -/
example : Adjacent 15 (runningExample.take 5) 12 14 ∧
    DiffIntervals 15 (runningExample.take 5) 12 14 ∧ Sep 15 (runningExample.take 5) 12 14 := by
  decide

set_option maxRecDepth 100000 in
/-- The example after \cref{lem:1342-separators}: adjacency cannot be dropped.  After the
prefix `3,5,1` of a permutation of `[7]` (`0`-based `2,4,0`) the stack is `{2,4} | {6,7}`
(`0`-based `{1,3} | {5,6}`), so `2` and `6` lie in different intervals although no letter
between them was read after a letter smaller than `2` -- and they are not adjacent. -/
example : stack 7 [2, 4, 0] = [{1, 3}, {5, 6}] := by decide

set_option maxRecDepth 100000 in
example : ¬ Adjacent 7 [2, 4, 0] 1 5 ∧ DiffIntervals 7 [2, 4, 0] 1 5 ∧ ¬ Sep 7 [2, 4, 0] 1 5 := by
  decide

set_option maxRecDepth 4000000 in
/-- The invariant itself, checked exhaustively at every prefix of the running example
\cref{ex:1342-scan} and at every pair of values. -/
example : ∀ k ∈ Finset.range 16, ∀ u ∈ Finset.range 15, ∀ v ∈ Finset.range 15,
    Adjacent 15 (runningExample.take k) u v → m 15 (runningExample.take k) < u →
      (DiffIntervals 15 (runningExample.take k) u v ↔ Sep 15 (runningExample.take k) u v) := by
  decide

set_option maxRecDepth 8000000 in
/-- The invariant, checked exhaustively over *every* legal prefix for `n = 4`: every prefix
of every permutation of `{0, 1, 2, 3}`, and every pair of values.  (The same check for
`n = 5` also passes; it is omitted here only because it costs about a minute.) -/
example : ∀ σ ∈ (List.range 4).permutations', ∀ k ∈ Finset.range 5,
    Legal 4 (σ.take k) → ∀ u ∈ Finset.range 4, ∀ v ∈ Finset.range 4,
      Adjacent 4 (σ.take k) u v → m 4 (σ.take k) < u →
        (DiffIntervals 4 (σ.take k) u v ↔ Sep 4 (σ.take k) u v) := by
  decide

end OneThreshold
end Av12453
