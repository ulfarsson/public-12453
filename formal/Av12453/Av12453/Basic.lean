/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
module

public import Mathlib
public import PermPatterns

@[expose] public section

/-!
# The patterns `β_d = ι_d ⊕ 231`

This file sets up the family of patterns studied in Section 2 of the paper
*Protected tails and polynomial-time enumeration of permutations avoiding a direct sum of an
increasing pattern and 231*, on top of the generic pattern-avoidance apparatus of the
`PermPatterns` library.

## Imports

This is the file where `Av12453` picks up Mathlib: it imports the root module `Mathlib`, and
every module of the library is downstream of it, so the paper-specific development may use
any part of Mathlib without further bookkeeping.  The reusable core `PermPatterns` is the
opposite: each of its modules imports only the Mathlib modules it needs, so a client of
`PermPatterns` alone pays for a small fraction of Mathlib.

## Translation table: the paper's notation and this development's

The paper numbers values and positions from `1`; **this development numbers both from `0`**.
The generic rows of the table — values, positions, suffixes, `ι_d`, `231`, standardization,
restriction and local rank — are in the root docstring of `PermPatterns.lean`; only the rows
for `β_d` are repeated here.

| paper | Lean |
|---|---|
| `β_d = ι_d ⊕ 231` | `beta d = iota d ++ [d + 1, d + 2, d]` |
| `β_1 = 1342` | `beta 1 = [0, 2, 3, 1]` (`Av12453.beta_one`, by `decide`) |
| `β_2 = 12453` | `beta 2 = [0, 1, 3, 4, 2]` (`Av12453.beta_two`, by `decide`) |

## Main definitions

* `Av12453.beta` : the pattern `β_d = ι_d ⊕ 231`, written `0`-based as in the table above.

## Main results

* `Av12453.beta_eq_directSum` : `β_d` is the direct sum `ι_d ⊕ 231`.
* `Av12453.beta_lt` : the direct-sum shape of `β_d`.
* `Av12453.contains_beta_iff` : `w` contains `β_d` iff there are positions
  `i₁ < ⋯ < i_d < j < k < l` with `w[i₁] < ⋯ < w[i_d] < w[l] < w[j] < w[k]`.
* `Av12453.contains_12453_iff` : the same for the paper's main case `β_2 = 12453`, written
  out with explicit letters.

Lists of positions are required to be `List.Pairwise (· < ·)`, which by
`List.isChain_iff_pairwise` is the same as the chain `i₁ < i₂ < ⋯` of the paper.  Letters
are written `w.getD i 0`; whenever `i < w.length` this is `w[i]` (`List.getD_eq_getElem`),
and every statement below carries the corresponding range hypothesis.
-/

namespace Av12453

open List

open PermPatterns

variable {u v w s ps : List ℕ} {τ τ' : List ℕ} {m x y : ℕ}

/-! ### The pattern `β_d` -/

/-- The pattern `β_d = ι_d ⊕ 231`, written `0`-based as `0, 1, …, d-1, d+1, d+2, d`. -/
def beta (d : ℕ) : List ℕ := iota d ++ [d + 1, d + 2, d]

@[simp] theorem length_beta (d : ℕ) : (beta d).length = d + 3 := by simp [beta]

/-- `β_1` is the paper's `1342`, written `0`-based. -/
theorem beta_one : beta 1 = [0, 2, 3, 1] := by decide

/-- `β_2` is the paper's `12453`, written `0`-based. -/
theorem beta_two : beta 2 = [0, 1, 3, 4, 2] := by decide

/-- `β_d` is literally the direct sum `ι_d ⊕ 231` of `PermPatterns.directSum`. -/
theorem beta_eq_directSum (d : ℕ) : beta d = directSum (iota d) pat231 := by
  simp [beta, directSum, pat231, Nat.add_comm]

/-- The direct-sum shape of `β_d`: every entry of `ι_d` is below the last three entries. -/
theorem beta_lt {d : ℕ} : ∀ x ∈ iota d, ∀ y ∈ [d + 1, d + 2, d], x < y := by
  intro x hx y hy
  have := mem_iota_lt hx
  fin_cases hy <;> omega

/-! ### Index characterization of `β_d`-containment -/

/--
**Index form of `β_d`-containment.**  A word contains `β_d = ι_d ⊕ 231` if and only if there
are positions `i₁ < ⋯ < i_d < j < k < l` (the list `ps = [i₁, …, i_d]` together with `j`,
`k`, `l`) whose letters satisfy `w[i₁] < ⋯ < w[i_d] < w[l] < w[j] < w[k]`.

Both chains are stated as `List.Pairwise (· < ·)`, which for the transitive relation `<` is
the chain of successive inequalities (`List.isChain_iff_pairwise`), and letters are written
`w.getD i 0 = w[i]` (`List.getD_eq_getElem`, applicable by the range hypotheses).
-/
theorem contains_beta_iff (w : List ℕ) (d : ℕ) :
    Contains w (beta d) ↔
      ∃ (ps : List ℕ) (j k l : ℕ),
        ps.length = d ∧ (∀ i ∈ ps, i < w.length) ∧
          j < w.length ∧ k < w.length ∧ l < w.length ∧
          (ps ++ [j, k, l]).Pairwise (· < ·) ∧
          (ps.map (fun i => w.getD i 0) ++
            [w.getD l 0, w.getD j 0, w.getD k 0]).Pairwise (· < ·) := by
  rw [contains_iff_picks]
  constructor
  · rintro ⟨qs, s, hp, hiso⟩
    obtain ⟨u₁, u₂, rfl, hu₁len, hiso₁, hiso₂, hcross⟩ :=
      hiso.exists_append (v₁ := iota d) (v₂ := [d + 1, d + 2, d]) beta_lt
    have hd1 : u₁.length = d := by simpa using hu₁len
    have hd2 : u₂.length = 3 := by simpa using hiso₂.length_eq
    have hqlen : qs.length = d + 3 := by
      rw [← hp.length]; simp [hd1, hd2]
    have hdrop : (qs.drop d).length = 3 := by simp [hqlen]
    obtain ⟨j, k, l, hjkl⟩ := List.length_eq_three.mp hdrop
    have hqs : qs = qs.take d ++ [j, k, l] := by
      conv_lhs => rw [← List.take_append_drop d qs]
      rw [hjkl]
    have htakelen : (qs.take d).length = d := by simp [hqlen]
    have hu₁ : u₁ = (qs.take d).map (fun i => w.getD i 0) :=
      calc u₁ = (u₁ ++ u₂).take d := (List.take_left' hd1).symm
        _ = (qs.map (fun i => w.getD i 0)).take d := by rw [hp.eq_map]
        _ = (qs.take d).map (fun i => w.getD i 0) := List.map_take.symm
    have hu₂ : u₂ = [w.getD j 0, w.getD k 0, w.getD l 0] :=
      calc u₂ = (u₁ ++ u₂).drop d := (List.drop_left' hd1).symm
        _ = (qs.map (fun i => w.getD i 0)).drop d := by rw [hp.eq_map]
        _ = (qs.drop d).map (fun i => w.getD i 0) := List.map_drop.symm
        _ = [w.getD j 0, w.getD k 0, w.getD l 0] := by rw [hjkl]; simp
    have hrange : ∀ i ∈ qs, i < w.length := hp.range
    have hjr : j < w.length := hrange j (by rw [hqs]; simp)
    have hkr : k < w.length := hrange k (by rw [hqs]; simp)
    have hlr : l < w.length := hrange l (by rw [hqs]; simp)
    rw [hu₂] at hiso₂
    obtain ⟨hlj, hjk⟩ := (orderIsomorphic_triple_iff (x := d + 1) (y := d + 2) (z := d)
      (by omega) (by omega)).mp hiso₂
    refine ⟨qs.take d, j, k, l, htakelen,
      fun i hi => hrange i (by rw [hqs]; exact List.mem_append_left _ hi), hjr, hkr, hlr, ?_, ?_⟩
    · rw [← hqs]; exact hp.incr
    · rw [List.pairwise_append]
      refine ⟨by rw [← hu₁]; exact (orderIsomorphic_iota_iff.mp hiso₁).2,
        pairwise_triple_iff.mpr ⟨hlj, hjk⟩, ?_⟩
      intro x hx y hy
      refine hcross x (by rw [hu₁]; exact hx) y ?_
      rw [hu₂]
      fin_cases hy <;> simp
  · rintro ⟨ps, j, k, l, hlen, hrange, hjr, hkr, hlr, hpos, hval⟩
    refine ⟨ps ++ [j, k, l], (ps ++ [j, k, l]).map (fun i => w.getD i 0), ?_, ?_⟩
    · refine picks_map hpos ?_
      intro i hi
      rcases List.mem_append.mp hi with h | h
      · exact hrange i h
      · fin_cases h <;> assumption
    · rw [List.map_append, List.pairwise_append] at *
      obtain ⟨hval₁, hval₂, hval₃⟩ := hval
      obtain ⟨hlj, hjk⟩ := pairwise_triple_iff.mp hval₂
      refine (orderIsomorphic_iota_iff.mpr ⟨by simp [hlen], hval₁⟩).append ?_ ?_ beta_lt
      · simp only [List.map_cons, List.map_nil]
        exact (orderIsomorphic_triple_iff (x := d + 1) (y := d + 2) (z := d) (by omega)
          (by omega)).mpr ⟨hlj, hjk⟩
      · intro x hx y hy
        simp only [List.map_cons, List.map_nil] at hy
        have h₁ : x < w.getD l 0 := hval₃ x hx _ (by simp)
        have h₂ : x < w.getD j 0 := hval₃ x hx _ (by simp)
        have h₃ : x < w.getD k 0 := hval₃ x hx _ (by simp)
        fin_cases hy <;> assumption

/--
The paper's main case `d = 2`, written out with explicit letters: `w` contains the paper's
`β_2 = 12453` — which `0`-based is the word `[0, 1, 3, 4, 2]` (`Av12453.beta_two`) — if and
only if there are positions `i₁ < i₂ < j < k < l` with `w[i₁] < w[i₂] < w[l] < w[j] < w[k]`.
-/
theorem contains_12453_iff (w : List ℕ) :
    Contains w [0, 1, 3, 4, 2] ↔
      ∃ (i₁ i₂ j k l : ℕ) (h₁ : i₁ < w.length) (h₂ : i₂ < w.length) (hj : j < w.length)
        (hk : k < w.length) (hl : l < w.length),
        i₁ < i₂ ∧ i₂ < j ∧ j < k ∧ k < l ∧
          w[i₁] < w[i₂] ∧ w[i₂] < w[l] ∧ w[l] < w[j] ∧ w[j] < w[k] := by
  rw [← beta_two, contains_beta_iff]
  constructor
  · rintro ⟨ps, j, k, l, hlen, hrange, hjr, hkr, hlr, hpos, hval⟩
    obtain ⟨i₁, i₂, rfl⟩ := List.length_eq_two.mp hlen
    have h₁ : i₁ < w.length := hrange i₁ (by simp)
    have h₂ : i₂ < w.length := hrange i₂ (by simp)
    have hmap : ([i₁, i₂] : List ℕ).map (fun a => w.getD a 0) ++
        [w.getD l 0, w.getD j 0, w.getD k 0] = [w[i₁], w[i₂], w[l], w[j], w[k]] := by
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂, List.getD_eq_getElem _ _ hjr,
        List.getD_eq_getElem _ _ hkr, List.getD_eq_getElem _ _ hlr]
    rw [show ([i₁, i₂] ++ [j, k, l] : List ℕ) = [i₁, i₂, j, k, l] from rfl,
      pairwise_five_iff] at hpos
    rw [hmap, pairwise_five_iff] at hval
    exact ⟨i₁, i₂, j, k, l, h₁, h₂, hjr, hkr, hlr, hpos.1, hpos.2.1, hpos.2.2.1, hpos.2.2.2,
      hval.1, hval.2.1, hval.2.2.1, hval.2.2.2⟩
  · rintro ⟨i₁, i₂, j, k, l, h₁, h₂, hjr, hkr, hlr, p₁, p₂, p₃, p₄, v₁, v₂, v₃, v₄⟩
    have hmap : ([i₁, i₂] : List ℕ).map (fun a => w.getD a 0) ++
        [w.getD l 0, w.getD j 0, w.getD k 0] = [w[i₁], w[i₂], w[l], w[j], w[k]] := by
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂, List.getD_eq_getElem _ _ hjr,
        List.getD_eq_getElem _ _ hkr, List.getD_eq_getElem _ _ hlr]
    refine ⟨[i₁, i₂], j, k, l, rfl, ?_, hjr, hkr, hlr, ?_, ?_⟩
    · intro i hi; fin_cases hi <;> assumption
    · rw [show ([i₁, i₂] ++ [j, k, l] : List ℕ) = [i₁, i₂, j, k, l] from rfl, pairwise_five_iff]
      exact ⟨p₁, p₂, p₃, p₄⟩
    · rw [hmap, pairwise_five_iff]
      exact ⟨v₁, v₂, v₃, v₄⟩

/-! ### Sanity checks against the paper's conventions -/

/-- The paper's `β_2 = 12453` occurs in the word `12453` (`0`-based: `[0, 1, 3, 4, 2]`). -/
example : Contains [0, 1, 3, 4, 2] (beta 2) :=
  ⟨[0, 1, 3, 4, 2], List.Sublist.refl _, beta_two ▸ OrderIsomorphic.refl _⟩

end Av12453
