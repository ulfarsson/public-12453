/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Mathlib.Data.Finset.Insert
import PermPatterns.Word

/-!
# Containment, avoidance and restriction

A word *contains* a pattern when some subsequence of it is order-isomorphic to the pattern,
and *avoids* it otherwise.  This file also introduces the restriction `w|_X` of a word to a
set of values, which is literally a `List.filter`.

## Main definitions

* `PermPatterns.Contains`, `PermPatterns.Avoids` : containment of a pattern and its negation.
* `PermPatterns.AvoidsAll` : avoidance of every pattern of a finite basis.
* `PermPatterns.restrict` : the restriction `w|_X` of `w` to the values lying in `X`.

## Main results

* `PermPatterns.contains_iff_picks` : containment stated at the level of positions.
* `PermPatterns.Contains.of_sublist`, `PermPatterns.Avoids.sublist` : monotonicity of
  containment under sublists.
* `PermPatterns.contains_congr_pattern`, `PermPatterns.contains_congr_word` : containment
  depends only on the order types of the pattern and of the word.
* `PermPatterns.avoidsAll_singleton`, `PermPatterns.avoidsAll_insert` : a basis is avoided
  one pattern at a time.
* `PermPatterns.restrict_sublist`, `PermPatterns.restrict_nodup` : `w|_X <+ w`, and `w|_X`
  has distinct entries when `w` does.
-/

namespace PermPatterns

open List

variable {u v w s ps : List ℕ} {τ τ' : List ℕ} {m x y : ℕ}

/-! ### Containment and avoidance -/

/--
`Contains w τ` : the word `w` contains the pattern `τ`, i.e. some subsequence of `w`
(a `List.Sublist`; the positions need not be adjacent) is order-isomorphic to `τ`.
-/
def Contains (w τ : List ℕ) : Prop := ∃ s, s <+ w ∧ OrderIsomorphic s τ

/-- `Avoids w τ` : the word `w` avoids the pattern `τ`. -/
def Avoids (w τ : List ℕ) : Prop := ¬ Contains w τ

theorem avoids_iff : Avoids w τ ↔ ¬ Contains w τ := Iff.rfl

/-- Containment stated at the level of positions. -/
theorem contains_iff_picks : Contains w τ ↔ ∃ ps s, Picks w ps s ∧ OrderIsomorphic s τ := by
  constructor
  · rintro ⟨s, hs, hiso⟩
    obtain ⟨ps, hp⟩ := exists_picks_of_sublist hs
    exact ⟨ps, s, hp, hiso⟩
  · rintro ⟨ps, s, hp, hiso⟩
    exact ⟨s, hp.sublist, hiso⟩

/-- Containment is monotone: a word containing `τ` still contains `τ` inside any larger
word. -/
theorem Contains.of_sublist (h : Contains v τ) (hvw : v <+ w) : Contains w τ := by
  obtain ⟨s, hs, hiso⟩ := h
  exact ⟨s, hs.trans hvw, hiso⟩

/-- Avoidance passes to subwords. -/
theorem Avoids.sublist (h : Avoids w τ) (hvw : v <+ w) : Avoids v τ :=
  fun hc => h (hc.of_sublist hvw)

/-- Containment depends only on the order type of the pattern. -/
theorem contains_congr_pattern (h : OrderIsomorphic τ τ') : Contains w τ ↔ Contains w τ' :=
  ⟨fun ⟨s, hs, hiso⟩ => ⟨s, hs, hiso.trans h⟩, fun ⟨s, hs, hiso⟩ => ⟨s, hs, hiso.trans h.symm⟩⟩

/-- Containment depends only on the order type of the word; this is why standardization
never has to be mentioned. -/
theorem contains_congr_word (h : OrderIsomorphic w v) : Contains w τ ↔ Contains v τ := by
  have key : ∀ {w v : List ℕ}, OrderIsomorphic w v → Contains w τ → Contains v τ := by
    rintro w v h ⟨s, hs, hiso⟩
    obtain ⟨ps, hp⟩ := exists_picks_of_sublist hs
    have hrange : ∀ i ∈ ps, i < v.length := fun i hi => h.length_eq ▸ hp.range i hi
    have hq : Picks v ps (ps.map (fun i => v.getD i 0)) := picks_map hp.incr hrange
    refine ⟨ps.map (fun i => v.getD i 0), hq.sublist, OrderIsomorphic.trans ?_ hiso⟩
    refine ⟨by rw [hq.length, hp.length], ?_⟩
    intro i j hi hj hi' hj'
    rw [hq.length] at hi hj
    rw [hp.length] at hi' hj'
    rw [hq.getElem_eq (by rw [hq.length]; omega) hi (hrange _ (List.getElem_mem hi)),
      hq.getElem_eq (by rw [hq.length]; omega) hj (hrange _ (List.getElem_mem hj)),
      hp.getElem_eq (by rw [hp.length]; omega) hi' (hp.range _ (List.getElem_mem hi')),
      hp.getElem_eq (by rw [hp.length]; omega) hj' (hp.range _ (List.getElem_mem hj'))]
    exact (h.lt_iff (hp.range _ (List.getElem_mem hi')) (hp.range _ (List.getElem_mem hj'))
      (hrange _ (List.getElem_mem hi)) (hrange _ (List.getElem_mem hj))).symm
  exact ⟨key h, key h.symm⟩

/-- Avoidance depends only on the order type of the word. -/
theorem avoids_congr_word (h : OrderIsomorphic w v) : Avoids w τ ↔ Avoids v τ :=
  not_congr (contains_congr_word h)

/-! ### Avoiding every pattern of a basis -/

/--
`AvoidsAll w B` : the word `w` avoids every pattern of the finite *basis* `B`, i.e. it lies
in the class `Av(B)`.  A single pattern `τ` is the singleton basis `{τ}`
(`PermPatterns.avoidsAll_singleton`).
-/
def AvoidsAll (w : List ℕ) (B : Finset (List ℕ)) : Prop := ∀ τ ∈ B, Avoids w τ

/-- Every word avoids the empty basis: `Av(∅)` is everything. -/
@[simp] theorem avoidsAll_empty : AvoidsAll w ∅ := by simp [AvoidsAll]

/-- Avoiding the singleton basis `{τ}` is avoiding `τ`. -/
@[simp] theorem avoidsAll_singleton : AvoidsAll w {τ} ↔ Avoids w τ := by
  simp [AvoidsAll]

/-- A basis is avoided one pattern at a time. -/
theorem avoidsAll_insert {B : Finset (List ℕ)} :
    AvoidsAll w (insert τ B) ↔ Avoids w τ ∧ AvoidsAll w B := by
  simp [AvoidsAll]

/-- Avoiding a basis is antitone in the basis: a smaller basis forbids less. -/
theorem AvoidsAll.mono {B B' : Finset (List ℕ)} (h : AvoidsAll w B') (hsub : B ⊆ B') :
    AvoidsAll w B := fun τ hτ => h τ (hsub hτ)

/-- Avoiding a basis passes to subwords. -/
theorem AvoidsAll.sublist {B : Finset (List ℕ)} (h : AvoidsAll w B) (hvw : v <+ w) :
    AvoidsAll v B := fun τ hτ => (h τ hτ).sublist hvw

/-! ### Restriction to a set of values -/

/-- The paper's `w|_X` : the subword of `w` formed by the letters lying in `X`. -/
def restrict (w : List ℕ) (X : ℕ → Prop) [DecidablePred X] : List ℕ :=
  w.filter (fun x => decide (X x))

@[simp]
theorem mem_restrict {X : ℕ → Prop} [DecidablePred X] {x : ℕ} :
    x ∈ restrict w X ↔ x ∈ w ∧ X x := by
  simp [restrict]

/-- `w|_X` is a subword of `w`. -/
theorem restrict_sublist {X : ℕ → Prop} [DecidablePred X] : restrict w X <+ w :=
  List.filter_sublist

/-- `w|_X` again has distinct entries. -/
theorem restrict_nodup {X : ℕ → Prop} [DecidablePred X] (h : w.Nodup) : (restrict w X).Nodup :=
  h.filter _

/-- Avoidance passes to restrictions. -/
theorem Avoids.restrict {X : ℕ → Prop} [DecidablePred X] (h : Avoids w τ) :
    Avoids (PermPatterns.restrict w X) τ :=
  h.sublist restrict_sublist

/-- `w\|_X` is literally a `List.filter`; this is the bridge between the two spellings. -/
theorem restrict_eq_filter {X : ℕ → Prop} [DecidablePred X] :
    restrict w X = w.filter (fun x => decide (X x)) := rfl

/-- A subword all of whose letters satisfy `p` is already a subword of `w.filter p`. -/
theorem sublist_filter_of_forall {p : ℕ → Bool} (h : s <+ w) (hp : ∀ a ∈ s, p a = true) :
    s <+ w.filter p := by
  have h' := h.filter p
  rwa [List.filter_eq_self.mpr hp] at h'

/-- A subword all of whose letters lie in `X` is a subword of the restriction `w\|_X`. -/
theorem sublist_restrict_of_forall {X : ℕ → Prop} [DecidablePred X] (h : s <+ w)
    (hx : ∀ x ∈ s, X x) : s <+ restrict w X := by
  rw [restrict_eq_filter]
  exact sublist_filter_of_forall h fun a ha => by simpa using hx a ha

end PermPatterns
