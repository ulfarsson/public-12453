/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Mathlib.Data.Fintype.Perm
import PermPatterns.Avoiders

/-!
# The bridge to Mathlib's `Equiv.Perm (Fin n)`

This library models a permutation as a word (a `List ℕ` that is a permutation of
`{0, …, n-1}`); Mathlib models it as an element of `Equiv.Perm (Fin n)`.  This file sets up
the dictionary between the two pictures and shows that pattern containment means the same
thing on both sides.

## Main definitions

* `PermPatterns.ofPerm` : the word `σ(0) σ(1) ⋯ σ(n-1)` of a permutation of `Fin n`.
* `PermPatterns.toPerm` : the permutation of `Fin n` of a word that is a permutation of
  `{0, …, n-1}`; it is computable, its inverse being `List.idxOf`.
* `PermPatterns.permEquiv` : the two pictures are the same, as an `Equiv`.
* `PermPatterns.PermContains`, `PermPatterns.PermAvoids` : containment and avoidance
  stated for `Equiv.Perm (Fin n)`, through an order embedding of positions.

## Main results

* `PermPatterns.ofPerm_isPermOf` : the word of a permutation of `Fin n` is a permutation of
  `{0, …, n-1}`.
* `PermPatterns.ofPerm_toPerm`, `PermPatterns.toPerm_ofPerm` : the two constructions are
  mutually inverse.
* `PermPatterns.permContains_iff_contains`, `PermPatterns.contains_iff_permContains` : the
  two notions of containment agree.
* `PermPatterns.card_avoiders_eq_fintypeCard`,
  `PermPatterns.card_avoiders_singleton_eq_fintypeCard` : the counting statement of
  `PermPatterns.avoiders` read on the `Equiv.Perm (Fin n)` side.
-/

namespace PermPatterns

open List

variable {n k : ℕ} {w v : List ℕ} {x : ℕ}

/-! ### The word of a permutation -/

/-- The word `σ(0) σ(1) ⋯ σ(n-1)` of a permutation of `Fin n`, in one-line notation. -/
def ofPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : List ℕ := List.ofFn fun i => (σ i : ℕ)

/-- The length of `ofPerm σ` is `n`. -/
@[simp] theorem length_ofPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : (ofPerm σ).length = n := by
  simp [ofPerm]

/-- The letter of `ofPerm σ` at position `i` is the value `σ i`. -/
@[simp] theorem getElem_ofPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) {i : ℕ}
    (hi : i < (ofPerm σ).length) : (ofPerm σ)[i] = (σ ⟨i, by simpa using hi⟩ : ℕ) := by
  simp [ofPerm]

/-- The word of a permutation of `Fin n` is a permutation of `{0, …, n-1}`. -/
theorem ofPerm_isPermOf {n : ℕ} (σ : Equiv.Perm (Fin n)) : IsPermOf n (ofPerm σ) := by
  refine isPermOf_iff.mpr ⟨?_, by simp, ?_⟩
  · exact List.nodup_ofFn.mpr fun a b hab => σ.injective (Fin.val_injective hab)
  · intro y hy
    simp only [ofPerm, List.mem_ofFn] at hy
    obtain ⟨i, rfl⟩ := hy
    exact (σ i).isLt

/-! ### The permutation of a word -/

/--
The permutation of `Fin n` of a word that is a permutation of `{0, …, n-1}`: the map
`i ↦ w[i]`.  It is bijective because `w` has distinct entries and uses every value below
`n`; the inverse map is `List.idxOf`, which keeps the definition computable.
-/
def toPerm {n : ℕ} (w : List ℕ) (h : IsPermOf n w) : Equiv.Perm (Fin n) where
  toFun i := ⟨w[(i : ℕ)]'(by rw [h.length]; exact i.isLt), h.lt_of_mem (List.getElem_mem _)⟩
  invFun j := ⟨w.idxOf (j : ℕ), by
    have hj : w.idxOf (j : ℕ) < w.length :=
      List.idxOf_lt_length_iff.mpr (h.mem_of_lt j.isLt)
    have hlen : w.length = n := h.length
    omega⟩
  left_inv i := by
    refine Fin.ext ?_
    simpa using h.nodup.idxOf_getElem (i : ℕ) (by rw [h.length]; exact i.isLt)
  right_inv j := by
    refine Fin.ext ?_
    simp

/-- The permutation `toPerm w h` sends `i` to the letter of `w` at position `i`. -/
@[simp] theorem toPerm_apply {n : ℕ} (w : List ℕ) (h : IsPermOf n w) (i : Fin n) :
    ((toPerm w h i : Fin n) : ℕ) = w[(i : ℕ)]'(by rw [h.length]; exact i.isLt) := rfl

/-- The inverse of `toPerm w h` sends `j` to the position of the value `j` in `w`. -/
@[simp] theorem toPerm_symm_apply {n : ℕ} (w : List ℕ) (h : IsPermOf n w) (j : Fin n) :
    (((toPerm w h).symm j : Fin n) : ℕ) = w.idxOf (j : ℕ) := rfl

/-- The word of the permutation of a word is the word itself. -/
theorem ofPerm_toPerm {n : ℕ} (w : List ℕ) (h : IsPermOf n w) : ofPerm (toPerm w h) = w := by
  refine List.ext_getElem (by simp [h.length]) fun i hi hi' => ?_
  rw [getElem_ofPerm, toPerm_apply]

/-- The permutation of the word of a permutation is the permutation itself. -/
theorem toPerm_ofPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (h : IsPermOf n (ofPerm σ)) :
    toPerm (ofPerm σ) h = σ := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [toPerm_apply, getElem_ofPerm]

/-- The two pictures of a permutation of `{0, …, n-1}` — a word and an element of
`Equiv.Perm (Fin n)` — are the same. -/
def permEquiv (n : ℕ) : Equiv.Perm (Fin n) ≃ {w : List ℕ // IsPermOf n w} where
  toFun σ := ⟨ofPerm σ, ofPerm_isPermOf σ⟩
  invFun w := toPerm w.1 w.2
  left_inv σ := toPerm_ofPerm σ _
  right_inv w := Subtype.ext (ofPerm_toPerm w.1 w.2)

/-! ### Containment on `Equiv.Perm (Fin n)` -/

/--
`PermContains σ τ` : the permutation `σ` of `Fin n` contains the pattern `τ` of `Fin k`,
i.e. there is an order embedding `f` of the positions of `τ` into those of `σ` under which
the letters of `σ` compare exactly as the letters of `τ` do.
-/
def PermContains {n k : ℕ} (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin k)) : Prop :=
  ∃ f : Fin k ↪o Fin n, ∀ i j, τ i < τ j ↔ σ (f i) < σ (f j)

/-- `PermAvoids σ τ` : the permutation `σ` avoids the pattern `τ`. -/
def PermAvoids {n k : ℕ} (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin k)) : Prop :=
  ¬ PermContains σ τ

/-- `PermAvoids` unfolds to the negation of `PermContains`. -/
theorem permAvoids_iff {n k : ℕ} {σ : Equiv.Perm (Fin n)} {τ : Equiv.Perm (Fin k)} :
    PermAvoids σ τ ↔ ¬ PermContains σ τ := Iff.rfl

/--
**The bridge.**  Containment of permutations of `Fin k` in permutations of `Fin n` is
containment of the corresponding words: an order embedding of positions is exactly a
`List.Sublist` of the one-line word, and the defining comparison condition is exactly order
isomorphism with the pattern word.
-/
theorem permContains_iff_contains {n k : ℕ} (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin k)) :
    PermContains σ τ ↔ Contains (ofPerm σ) (ofPerm τ) := by
  constructor
  · rintro ⟨f, hf⟩
    have hrange : ∀ i ∈ List.ofFn fun a : Fin k => ((f a : Fin n) : ℕ), i < (ofPerm σ).length := by
      intro i hi
      simp only [List.mem_ofFn] at hi
      obtain ⟨a, rfl⟩ := hi
      simp
    have hincr : (List.ofFn fun a : Fin k => ((f a : Fin n) : ℕ)).Pairwise (· < ·) :=
      List.pairwise_ofFn.mpr fun a b hab => f.strictMono hab
    have hs : (List.ofFn fun a : Fin k => ((f a : Fin n) : ℕ)).map
        (fun i => (ofPerm σ).getD i 0) = List.ofFn fun a : Fin k => ((σ (f a) : Fin n) : ℕ) := by
      rw [List.map_ofFn]
      refine congrArg List.ofFn (funext fun a => ?_)
      simp only [Function.comp_apply]
      rw [List.getD_eq_getElem _ _ (by simp), getElem_ofPerm]
    refine ⟨_, (picks_map hincr hrange).sublist, ?_⟩
    rw [hs]
    refine ⟨by simp, fun a b ha hb ha' hb' => ?_⟩
    simp only [List.length_ofFn] at ha hb
    rw [List.getElem_ofFn, List.getElem_ofFn, getElem_ofPerm, getElem_ofPerm]
    exact (hf ⟨a, ha⟩ ⟨b, hb⟩).symm
  · rintro ⟨s, hsub, hiso⟩
    obtain ⟨ps, hp⟩ := exists_picks_of_sublist hsub
    have hpk : ps.length = k := by rw [← hp.length, hiso.length_eq, length_ofPerm]
    have hsk : s.length = k := by rw [hiso.length_eq, length_ofPerm]
    have hrange : ∀ a : Fin k, (ps[(a : ℕ)]'(by rw [hpk]; exact a.isLt)) < n := fun a => by
      simpa using hp.range _ (List.getElem_mem _)
    have hmono : StrictMono fun a : Fin k =>
        (⟨ps[(a : ℕ)]'(by rw [hpk]; exact a.isLt), hrange a⟩ : Fin n) := fun a b hab =>
      (List.pairwise_iff_getElem.mp hp.incr) _ _ _ _ hab
    refine ⟨OrderEmbedding.ofStrictMono _ hmono, fun a b => ?_⟩
    have key : ∀ c : Fin k, s[(c : ℕ)]'(by rw [hsk]; exact c.isLt) =
        ((σ ⟨ps[(c : ℕ)]'(by rw [hpk]; exact c.isLt), hrange c⟩ : Fin n) : ℕ) := fun c => by
      rw [hp.getElem_eq (by rw [hsk]; exact c.isLt) (by rw [hpk]; exact c.isLt)
        (by simpa using hrange c), getElem_ofPerm]
    have hτ : ∀ c : Fin k, (ofPerm τ)[(c : ℕ)]'(by simp) = ((τ c : Fin k) : ℕ) :=
      fun c => by rw [getElem_ofPerm]
    have := hiso.lt_iff (i := (a : ℕ)) (j := (b : ℕ)) (by rw [hsk]; exact a.isLt)
      (by rw [hsk]; exact b.isLt) (by simp) (by simp)
    rw [key a, key b, hτ a, hτ b] at this
    simpa using this.symm

/-- Containment on `Equiv.Perm (Fin n)` is decidable, through the bridge to words. -/
instance decidablePermContains {n k : ℕ} (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin k)) :
    Decidable (PermContains σ τ) :=
  decidable_of_iff _ (permContains_iff_contains σ τ).symm

/-- Avoidance on `Equiv.Perm (Fin n)` is decidable, being the negation of containment. -/
instance decidablePermAvoids {n k : ℕ} (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin k)) :
    Decidable (PermAvoids σ τ) :=
  inferInstanceAs (Decidable ¬ PermContains σ τ)

/-- The bridge read the other way: containment of words that are permutations is
containment of the corresponding permutations. -/
theorem contains_iff_permContains {n k : ℕ} {w v : List ℕ} (hw : IsPermOf n w)
    (hv : IsPermOf k v) : Contains w v ↔ PermContains (toPerm w hw) (toPerm v hv) := by
  rw [permContains_iff_contains, ofPerm_toPerm, ofPerm_toPerm]

/-! ### Counting -/

/-- The avoiders of a basis `B`, counted on the `Equiv.Perm (Fin n)` side. -/
theorem card_avoiders_eq_fintypeCard (n : ℕ) (B : Finset (List ℕ)) :
    (avoiders n B).card = Fintype.card {σ : Equiv.Perm (Fin n) // AvoidsAll (ofPerm σ) B} := by
  rw [← Fintype.card_coe]
  refine Fintype.card_congr ?_
  refine ⟨fun w => ⟨toPerm w.1 (mem_avoiders.mp w.2).1, ?_⟩,
    fun σ => ⟨ofPerm σ.1, mem_avoiders.mpr ⟨ofPerm_isPermOf _, σ.2⟩⟩, ?_, ?_⟩
  · rw [ofPerm_toPerm]; exact (mem_avoiders.mp w.2).2
  · exact fun w => Subtype.ext (ofPerm_toPerm w.1 (mem_avoiders.mp w.2).1)
  · exact fun σ => Subtype.ext (toPerm_ofPerm σ.1 (ofPerm_isPermOf σ.1))

/-- The avoiders of a single pattern `τ`, counted on the `Equiv.Perm (Fin n)` side. -/
theorem card_avoiders_singleton_eq_fintypeCard (n : ℕ) {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    (avoiders n {ofPerm τ}).card = Fintype.card {σ : Equiv.Perm (Fin n) // PermAvoids σ τ} := by
  rw [card_avoiders_eq_fintypeCard]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun σ => ?_)
  rw [avoidsAll_singleton, Avoids, permAvoids_iff, permContains_iff_contains]

end PermPatterns
