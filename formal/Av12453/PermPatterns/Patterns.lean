/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
module

public import Mathlib.Tactic.IntervalCases
public import PermPatterns.Containment

@[expose] public section

/-!
# The patterns `231` and `ι_d`, and increasing subsequences

The concrete patterns used throughout, the characterizations of order isomorphism with them,
and the vocabulary of increasing `d`-subsequences and `d`-triggers.

## Main definitions

* `PermPatterns.pat231`, `PermPatterns.iota` : the patterns `231` and `ι_d = 12⋯d`, written
  `0`-based as `[1, 2, 0]` and `[0, 1, …, d-1]`.
* `PermPatterns.IncrSubseq`, `PermPatterns.IsTriggerAt`, `PermPatterns.IsTrigger` :
  increasing `d`-subsequences and `d`-triggers.

## Main results

* `PermPatterns.orderIsomorphic_iota_iff` : a word is order-isomorphic to `ι_d` exactly when it is
  a strictly increasing word of length `d`.
* `PermPatterns.orderIsomorphic_triple_iff` : order isomorphism with a three-letter `231` pattern.
* `PermPatterns.contains_231_iff` : `w` contains `231` iff there are positions `i < j < k`
  with `w[k] < w[i] < w[j]`.
* `PermPatterns.isTriggerAt_one_iff` : every letter is a `1`-trigger, and only letters are.
-/

namespace PermPatterns

open List

variable {u v w s ps : List ℕ} {τ τ' : List ℕ} {m x y : ℕ}

/-! ### The patterns `231` and `ι_d` -/

/-- The pattern `231`, written `0`-based. -/
def pat231 : List ℕ := [1, 2, 0]

/-- The increasing pattern `ι_d = 12⋯d`, written `0`-based as `0, 1, …, d-1`. -/
def iota (d : ℕ) : List ℕ := List.range d

@[simp] theorem length_iota (d : ℕ) : (iota d).length = d := by simp [iota]

theorem getElem_iota {d a : ℕ} (h : a < (iota d).length) : (iota d)[a] = a := by
  simp [iota]

theorem mem_iota_lt {d z : ℕ} (h : z ∈ iota d) : z < d := by
  simpa [iota] using h

/-! ### Order isomorphism with the concrete patterns -/

/-- A word is order-isomorphic to `ι_d` exactly when it is a strictly increasing word of
length `d`. -/
theorem orderIsomorphic_iota_iff {d : ℕ} :
    OrderIsomorphic u (iota d) ↔ u.length = d ∧ u.Pairwise (· < ·) := by
  constructor
  · intro h
    have hlen : u.length = d := by simpa using h.length_eq
    have hlen' : (iota d).length = d := length_iota d
    refine ⟨hlen, List.pairwise_iff_getElem.mpr fun i j hi hj hij => ?_⟩
    have hlt := h.lt_iff hi hj (by omega) (by omega)
    rw [getElem_iota, getElem_iota] at hlt
    exact hlt.mpr (by omega)
  · rintro ⟨hlen, hp⟩
    refine ⟨by simp [hlen], ?_⟩
    intro i j hi hj hi' hj'
    rw [getElem_iota, getElem_iota]
    constructor
    · intro hlt
      have hij : i < j := by
        by_contra hij
        rcases Nat.lt_or_ge j i with h' | h'
        · exact absurd hlt (lt_asymm ((List.pairwise_iff_getElem.mp hp) j i hj hi h'))
        · have hEq : i = j := by omega
          subst hEq
          exact absurd hlt (lt_irrefl _)
      omega
    · intro hij
      exact (List.pairwise_iff_getElem.mp hp) i j hi hj (by omega)

/-- A three-letter word is order-isomorphic to a `231` pattern `[x, y, z]` (that is,
`z < x < y`) exactly when its last letter is smallest and its first letter is in the
middle. -/
theorem orderIsomorphic_triple_iff {p q r x y z : ℕ} (hzx : z < x) (hxy : x < y) :
    OrderIsomorphic [p, q, r] [x, y, z] ↔ r < p ∧ p < q := by
  constructor
  · intro h
    have h1 := h.lt_iff (i := 0) (j := 1) (by simp) (by simp) (by simp) (by simp)
    have h2 := h.lt_iff (i := 2) (j := 0) (by simp) (by simp) (by simp) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h1 h2
    exact ⟨h2.mpr (by omega), h1.mpr (by omega)⟩
  · rintro ⟨hrp, hpq⟩
    refine ⟨rfl, ?_⟩
    intro i j hi hj hi' hj'
    simp only [List.length_cons, List.length_nil] at hi hj
    interval_cases i <;> interval_cases j <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> omega

/-! ### Index characterization of `231`-containment -/

/--
**Index form of `231`-containment.**  A word contains `231` if and only if there are
positions `i < j < k` with `w[k] < w[i] < w[j]`.
-/
theorem contains_231_iff (w : List ℕ) :
    Contains w pat231 ↔
      ∃ (i j k : ℕ) (hi : i < w.length) (hj : j < w.length) (hk : k < w.length),
        i < j ∧ j < k ∧ w[k] < w[i] ∧ w[i] < w[j] := by
  constructor
  · rw [contains_iff_picks]
    rintro ⟨ps, s, hp, hiso⟩
    have hlen : ps.length = 3 := by rw [← hp.length, hiso.length_eq]; rfl
    obtain ⟨i, j, k, rfl⟩ := List.length_eq_three.mp hlen
    obtain ⟨hij, hjk⟩ := pairwise_triple_iff.mp hp.incr
    have hi : i < w.length := hp.range i (by simp)
    have hj : j < w.length := hp.range j (by simp)
    have hk : k < w.length := hp.range k (by simp)
    have hs : s.length = 3 := by rw [hp.length]; simp
    have e0 : s[0]'(by omega) = w[i] := by
      simpa using hp.getElem_eq (a := 0) (by omega) (by simp) (by simpa using hi)
    have e1 : s[1]'(by omega) = w[j] := by
      simpa using hp.getElem_eq (a := 1) (by omega) (by simp) (by simpa using hj)
    have e2 : s[2]'(by omega) = w[k] := by
      simpa using hp.getElem_eq (a := 2) (by omega) (by simp) (by simpa using hk)
    have hs3 : s = [w[i], w[j], w[k]] := by
      refine List.ext_getElem (by simp [hs]) fun n h₁ h₂ => ?_
      simp only [hs] at h₁
      interval_cases n
      · simpa using e0
      · simpa using e1
      · simpa using e2
    rw [hs3] at hiso
    obtain ⟨h1, h2⟩ := (orderIsomorphic_triple_iff (p := w[i]) (q := w[j]) (r := w[k]) (x := 1)
      (y := 2) (z := 0) (by norm_num) (by norm_num)).mp hiso
    exact ⟨i, j, k, hi, hj, hk, hij, hjk, h1, h2⟩
  · rintro ⟨i, j, k, hi, hj, hk, hij, hjk, h1, h2⟩
    exact ⟨[w[i], w[j], w[k]], triple_sublist hi hj hk hij hjk,
      (orderIsomorphic_triple_iff (x := 1) (y := 2) (z := 0) (by norm_num) (by norm_num)).mpr
        ⟨h1, h2⟩⟩

/-! ### Increasing `d`-subsequences and `d`-triggers -/

/--
An *increasing `d`-subsequence* of `w` is a choice of positions `i₁ < ⋯ < i_d` with
`w[i₁] < ⋯ < w[i_d]`; the positions need not be adjacent.  Here `ps` is the list of
positions.
-/
structure IncrSubseq (w : List ℕ) (d : ℕ) (ps : List ℕ) : Prop where
  /-- There are `d` positions. -/
  length : ps.length = d
  /-- The positions are in range. -/
  range : ∀ i ∈ ps, i < w.length
  /-- The positions increase. -/
  pos : ps.Pairwise (· < ·)
  /-- The letters at those positions increase. -/
  val : (ps.map (fun i => w.getD i 0)).Pairwise (· < ·)

/-- `IsTriggerAt w d j` : the letter of `w` at position `j` is the last entry of an
increasing `d`-subsequence, i.e. it is a *`d`-trigger*. -/
def IsTriggerAt (w : List ℕ) (d j : ℕ) : Prop :=
  ∃ ps, IncrSubseq w d ps ∧ ps.getLast? = some j

/-- A letter `c` of `w` is a *`d`-trigger* when it is the last entry of an increasing
`d`-subsequence. -/
def IsTrigger (w : List ℕ) (d c : ℕ) : Prop :=
  ∃ j, IsTriggerAt w d j ∧ w.getD j 0 = c

theorem IsTriggerAt.lt_length {d j : ℕ} (h : IsTriggerAt w d j) : j < w.length := by
  obtain ⟨ps, hps, hlast⟩ := h
  exact hps.range j (List.mem_of_getLast? hlast)

/-- Every letter is a `1`-trigger, and only letters are. -/
theorem isTriggerAt_one_iff {j : ℕ} : IsTriggerAt w 1 j ↔ j < w.length := by
  refine ⟨IsTriggerAt.lt_length, fun hj => ⟨[j], ⟨rfl, ?_, by simp, by simp⟩, by simp⟩⟩
  intro i hi
  fin_cases hi
  exact hj

/-! ### Sanity checks -/

/-- `231` occurs in the word `231` itself (`0`-based: `[1, 2, 0]`). -/
example : Contains [1, 2, 0] pat231 :=
  (contains_231_iff _).mpr ⟨0, 1, 2, by simp, by simp, by simp, by omega, by omega, by decide,
    by decide⟩

-- An increasing word avoids `231`.
set_option linter.unnecessarySeqFocus false in
example : Avoids [0, 1, 2] pat231 := by
  rw [Avoids, contains_231_iff]
  rintro ⟨i, j, k, hi, hj, hk, hij, hjk, h1, h2⟩
  simp only [List.length_cons, List.length_nil] at hi hj hk
  interval_cases i <;> interval_cases j <;> interval_cases k <;> simp_all

end PermPatterns
