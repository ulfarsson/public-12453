/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic.FinCases

/-!
# Words, order isomorphism and subwords

The base layer of the `PermPatterns` library: words on `ℕ`, the relation of being
order-isomorphic, and the description of a subword by the list of positions it is read off
at.  Values and positions are `0`-based; see the translation table in `PermPatterns.lean`.

## Main definitions

* `PermPatterns.IsWordOn`, `PermPatterns.IsPermOf` : a word on a finite alphabet, and a word
  that is a permutation of `{0, 1, …, n-1}`.
* `PermPatterns.OrderIsomorphic` : two words have the same length and the same relative order at
  every pair of positions.
* `PermPatterns.Picks w ps s` : `s` is the subword of `w` read off at the strictly increasing
  list of positions `ps`.  This is the index-level description of `s <+ w`.

## Main results

* `PermPatterns.isPermOf_iff` : a word is a permutation of `{0, …, n-1}` exactly when it has
  distinct entries, length `n` and entries below `n`.
* `PermPatterns.orderIsomorphic_equivalence` : order isomorphism is an equivalence relation.
* `PermPatterns.orderIsomorphic_map_add`, `PermPatterns.OrderIsomorphic.reverse` :
  translation and reversal preserve order isomorphism.
* `PermPatterns.OrderIsomorphic.append`, `PermPatterns.OrderIsomorphic.exists_append` :
  order isomorphism and the direct sum of two words.
* `PermPatterns.Picks.sublist`, `PermPatterns.exists_picks_of_sublist` : `Picks` and
  `List.Sublist` describe the same subwords.
* `PermPatterns.triple_sublist` : three letters at increasing positions form a subword.
-/

namespace PermPatterns

open List

variable {u v w s ps : List ℕ} {τ τ' : List ℕ} {m x y : ℕ}

/-! ### Auxiliary list lemmas -/

private theorem getElem_append_add {α : Type*} {v₁ v₂ : List α} {b : ℕ} (hb : b < v₂.length)
    {h : v₁.length + b < (v₁ ++ v₂).length} : (v₁ ++ v₂)[v₁.length + b] = v₂[b] := by
  simp [List.getElem_append_right]

/-- Three entries are increasing iff they form a chain. -/
theorem pairwise_triple_iff {a b c : ℕ} :
    ([a, b, c] : List ℕ).Pairwise (· < ·) ↔ a < b ∧ b < c := by
  simp; omega

/-- Five entries are increasing iff they form a chain. -/
theorem pairwise_five_iff {a b c e f : ℕ} :
    ([a, b, c, e, f] : List ℕ).Pairwise (· < ·) ↔ a < b ∧ b < c ∧ c < e ∧ e < f := by
  simp; omega

/-! ### Words -/

/-- `w` is a word on the finite ordered alphabet `I`: it uses each value of `I` exactly
once (the paper's "permutation of `I`"). -/
def IsWordOn (w : List ℕ) (I : Finset ℕ) : Prop := w.Nodup ∧ w.toFinset = I

/-- `w` is a permutation of `[n]`, written as a word.  Values are `0`-based, so `[n]` is
`{0, 1, …, n-1} = List.range n` (the paper's `{1, …, n}`; see the translation table). -/
def IsPermOf (n : ℕ) (w : List ℕ) : Prop := w.Perm (List.range n)

theorem IsPermOf.nodup {n : ℕ} (h : IsPermOf n w) : w.Nodup :=
  h.nodup_iff.mpr List.nodup_range

theorem IsPermOf.length {n : ℕ} (h : IsPermOf n w) : w.length = n := by
  simpa using h.length_eq

/-- Every letter of a permutation of `{0, …, n-1}` is below `n`. -/
theorem IsPermOf.lt_of_mem {n : ℕ} (h : IsPermOf n w) (hx : x ∈ w) : x < n := by
  simpa using h.mem_iff.mp hx

/-- Every value below `n` is a letter of a permutation of `{0, …, n-1}`. -/
theorem IsPermOf.mem_of_lt {n : ℕ} (h : IsPermOf n w) (hx : x < n) : x ∈ w :=
  h.mem_iff.mpr (by simpa using hx)

/-- A word is a permutation of `{0, …, n-1}` exactly when it has distinct entries, length
`n`, and all its entries below `n`. -/
theorem isPermOf_iff {n : ℕ} : IsPermOf n w ↔ w.Nodup ∧ w.length = n ∧ ∀ x ∈ w, x < n := by
  refine ⟨fun h => ⟨h.nodup, h.length, fun x hx => h.lt_of_mem hx⟩, ?_⟩
  rintro ⟨hnd, hlen, hlt⟩
  have hsub : w ⊆ List.range n := fun x hx => List.mem_range.mpr (hlt x hx)
  exact (hnd.subperm hsub).perm_of_length_le (by simp [hlen])

/-! ### Order isomorphism -/

/--
Two words are *order-isomorphic* when they have the same length and, at every pair of
positions, their entries compare in the same way.  Equivalently, they have the same
standardization.
-/
def OrderIsomorphic (u v : List ℕ) : Prop :=
  u.length = v.length ∧
    ∀ (i j : ℕ) (_hiu : i < u.length) (_hju : j < u.length)
      (_hiv : i < v.length) (_hjv : j < v.length), u[i] < u[j] ↔ v[i] < v[j]

theorem OrderIsomorphic.length_eq (h : OrderIsomorphic u v) : u.length = v.length := h.1

theorem OrderIsomorphic.lt_iff (h : OrderIsomorphic u v) {i j : ℕ} (hiu : i < u.length)
    (hju : j < u.length) (hiv : i < v.length) (hjv : j < v.length) : u[i] < u[j] ↔ v[i] < v[j] :=
  h.2 i j hiu hju hiv hjv

@[refl]
theorem OrderIsomorphic.refl (u : List ℕ) : OrderIsomorphic u u := ⟨rfl, fun _ _ _ _ _ _ => Iff.rfl⟩

theorem OrderIsomorphic.symm (h : OrderIsomorphic u v) : OrderIsomorphic v u :=
  ⟨h.1.symm, fun i j hiv hjv hiu hju => (h.2 i j hiu hju hiv hjv).symm⟩

theorem OrderIsomorphic.trans (h₁ : OrderIsomorphic u v) (h₂ : OrderIsomorphic v w) :
    OrderIsomorphic u w := by
  obtain ⟨hl₁, hr₁⟩ := h₁
  obtain ⟨hl₂, hr₂⟩ := h₂
  refine ⟨hl₁.trans hl₂, fun i j hiu hju hiw hjw => ?_⟩
  have hiv : i < v.length := by omega
  have hjv : j < v.length := by omega
  exact (hr₁ i j hiu hju hiv hjv).trans (hr₂ i j hiv hjv hiw hjw)

/-- Order isomorphism of words is an equivalence relation. -/
theorem orderIsomorphic_equivalence : Equivalence OrderIsomorphic :=
  ⟨OrderIsomorphic.refl, OrderIsomorphic.symm, OrderIsomorphic.trans⟩

/-- Order-isomorphic words have distinct entries simultaneously. -/
theorem OrderIsomorphic.nodup (h : OrderIsomorphic u v) (hu : u.Nodup) : v.Nodup := by
  have hu' : List.Pairwise (· ≠ ·) u := hu
  rw [List.pairwise_iff_getElem] at hu'
  change List.Pairwise (· ≠ ·) v
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i < u.length := by rw [h.length_eq]; exact hi
  have hj' : j < u.length := by rw [h.length_eq]; exact hj
  rcases lt_or_gt_of_ne (hu' i j hi' hj' hij) with hlt | hlt
  · exact ne_of_lt ((h.lt_iff hi' hj' hi hj).mp hlt)
  · exact ne_of_gt ((h.lt_iff hj' hi' hj hi).mp hlt)

/-- Translating every letter of a word by a constant does not change its order type. -/
theorem orderIsomorphic_map_add (w : List ℕ) (c : ℕ) : OrderIsomorphic w (w.map (· + c)) := by
  refine ⟨by simp, fun i j hi hj hi' hj' => ?_⟩
  simp only [List.getElem_map]
  omega

/-- Reversal preserves order isomorphism. -/
theorem OrderIsomorphic.reverse {u v : List ℕ} (h : OrderIsomorphic u v) :
    OrderIsomorphic u.reverse v.reverse := by
  have hlen : u.length = v.length := h.length_eq
  refine ⟨by simp [hlen], fun i j hi hj hi' hj' => ?_⟩
  simp only [List.length_reverse] at hi hj hi' hj'
  have e1 : v.length - 1 - i = u.length - 1 - i := by omega
  have e2 : v.length - 1 - j = u.length - 1 - j := by omega
  rw [List.getElem_reverse, List.getElem_reverse, List.getElem_reverse, List.getElem_reverse]
  simp only [e1, e2]
  exact h.lt_iff (by omega) (by omega) (by omega) (by omega)

/-- The direct sum of order isomorphisms: if `u₁` sits below `u₂` and `v₁` below `v₂`, then
order isomorphisms of the halves assemble.  This is the paper's `⊕`. -/
theorem OrderIsomorphic.append {u₁ u₂ v₁ v₂ : List ℕ} (h₁ : OrderIsomorphic u₁ v₁)
    (h₂ : OrderIsomorphic u₂ v₂) (hu : ∀ x ∈ u₁, ∀ y ∈ u₂, x < y)
    (hv : ∀ x ∈ v₁, ∀ y ∈ v₂, x < y) : OrderIsomorphic (u₁ ++ u₂) (v₁ ++ v₂) := by
  have hlen : u₁.length = v₁.length := h₁.length_eq
  have hlen₂ : u₂.length = v₂.length := h₂.length_eq
  refine ⟨by simp [hlen, hlen₂], ?_⟩
  intro i j hiu hju hiv hjv
  simp only [List.length_append] at hiu hju hiv hjv
  by_cases hi : i < u₁.length <;> by_cases hj : j < u₁.length
  · rw [List.getElem_append_left hi, List.getElem_append_left hj,
      List.getElem_append_left (show i < v₁.length by omega),
      List.getElem_append_left (show j < v₁.length by omega)]
    exact h₁.lt_iff hi hj (by omega) (by omega)
  · rw [List.getElem_append_left hi, List.getElem_append_right (by omega),
      List.getElem_append_left (show i < v₁.length by omega),
      List.getElem_append_right (by omega)]
    exact iff_of_true (hu _ (List.getElem_mem _) _ (List.getElem_mem _))
      (hv _ (List.getElem_mem _) _ (List.getElem_mem _))
  · rw [List.getElem_append_right (by omega), List.getElem_append_left hj,
      List.getElem_append_right (by omega),
      List.getElem_append_left (show j < v₁.length by omega)]
    exact iff_of_false (lt_asymm (hu _ (List.getElem_mem _) _ (List.getElem_mem _)))
      (lt_asymm (hv _ (List.getElem_mem _) _ (List.getElem_mem _)))
  · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega),
      List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
    simp only [hlen]
    exact h₂.lt_iff (by omega) (by omega) (by omega) (by omega)

/-- The converse decomposition: an order isomorphism onto a direct sum `v₁ ++ v₂` splits the
source word in the same way. -/
theorem OrderIsomorphic.exists_append {v₁ v₂ : List ℕ} (hv : ∀ x ∈ v₁, ∀ y ∈ v₂, x < y)
    (h : OrderIsomorphic s (v₁ ++ v₂)) :
    ∃ u₁ u₂, s = u₁ ++ u₂ ∧ u₁.length = v₁.length ∧ OrderIsomorphic u₁ v₁ ∧ OrderIsomorphic u₂ v₂ ∧
      ∀ x ∈ u₁, ∀ y ∈ u₂, x < y := by
  have hlen : s.length = v₁.length + v₂.length := by simpa using h.length_eq
  refine ⟨s.take v₁.length, s.drop v₁.length, (List.take_append_drop _ _).symm,
    by simp; omega, ?_, ?_, ?_⟩
  · refine ⟨by simp; omega, ?_⟩
    intro i j hi hj hi' hj'
    simp only [List.length_take] at hi hj
    rw [List.getElem_take, List.getElem_take]
    have hlt := h.lt_iff (i := i) (j := j) (by omega) (by omega) (by simp; omega) (by simp; omega)
    rwa [List.getElem_append_left (by omega), List.getElem_append_left (by omega)] at hlt
  · refine ⟨by simp; omega, ?_⟩
    intro i j hi hj hi' hj'
    simp only [List.length_drop] at hi hj
    rw [List.getElem_drop, List.getElem_drop]
    have hlt := h.lt_iff (i := v₁.length + i) (j := v₁.length + j) (by omega) (by omega)
      (by simp; omega) (by simp; omega)
    rwa [getElem_append_add hi', getElem_append_add hj'] at hlt
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨b, hb, rfl⟩ := List.mem_iff_getElem.mp hy
    simp only [List.length_take] at ha
    simp only [List.length_drop] at hb
    rw [List.getElem_take, List.getElem_drop]
    have hlt := h.lt_iff (i := a) (j := v₁.length + b) (by omega) (by omega) (by simp; omega)
      (by simp; omega)
    rw [List.getElem_append_left (by omega), getElem_append_add (by omega)] at hlt
    exact hlt.mpr (hv _ (List.getElem_mem _) _ (List.getElem_mem _))

/-! ### Subwords described by their positions -/

/--
`Picks w ps s` says that `s` is the subword of `w` read off at the positions `ps`: the
positions are strictly increasing and in range, and the `a`-th letter of `s` is the letter
of `w` at position `ps[a]`.  This is the index-level form of `s <+ w`; see `Picks.sublist`
and `exists_picks_of_sublist`.
-/
structure Picks (w : List ℕ) (ps : List ℕ) (s : List ℕ) : Prop where
  /-- The positions are strictly increasing. -/
  incr : ps.Pairwise (· < ·)
  /-- The positions are in range. -/
  range : ∀ i ∈ ps, i < w.length
  /-- There is one letter per position. -/
  length : s.length = ps.length
  /-- The letters of `s` are the letters of `w` at the given positions. -/
  val : ∀ a : ℕ, s[a]? = (ps[a]?).bind (fun i => w[i]?)

theorem Picks.getElem_eq (h : Picks w ps s) {a : ℕ} (ha : a < s.length) (hb : a < ps.length)
    (hc : ps[a] < w.length) : s[a] = w[ps[a]] := by
  have hval := h.val a
  rw [List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb] at hval
  simpa [List.getElem?_eq_getElem hc] using hval

theorem Picks.eq_map (h : Picks w ps s) : s = ps.map (fun i => w.getD i 0) := by
  refine List.ext_getElem? fun a => ?_
  rw [h.val a, List.getElem?_map]
  cases hpa : ps[a]? with
  | none => simp
  | some i =>
    have hi : i < w.length := h.range i (List.mem_of_getElem? hpa)
    simp [List.getElem?_eq_getElem hi]

/-- The subword read off at an increasing list of in-range positions is a sublist. -/
theorem Picks.sublist (h : Picks w ps s) : s <+ w := by
  have hmono : StrictMono (fun a => if ha : a < ps.length then ps[a] else w.length + a) := by
    intro a b hab
    dsimp only
    split_ifs with ha hb hb
    · exact (List.pairwise_iff_getElem.mp h.incr) a b ha hb hab
    · have : ps[a] < w.length := h.range _ (List.getElem_mem ha)
      omega
    · omega
    · omega
  refine List.sublist_of_orderEmbedding_getElem?_eq (OrderEmbedding.ofStrictMono _ hmono) ?_
  intro a
  rw [OrderEmbedding.coe_ofStrictMono, h.val a]
  by_cases ha : a < ps.length
  · rw [dif_pos ha, List.getElem?_eq_getElem ha]
    rfl
  · rw [dif_neg ha, List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    rfl

/-- The letters of `w` at an increasing list of in-range positions form a subword. -/
theorem picks_map (hincr : ps.Pairwise (· < ·)) (hrange : ∀ i ∈ ps, i < w.length) :
    Picks w ps (ps.map (fun i => w.getD i 0)) where
  incr := hincr
  range := hrange
  length := by simp
  val := by
    intro a
    rw [List.getElem?_map]
    cases hpa : ps[a]? with
    | none => simp
    | some i =>
      have hi : i < w.length := hrange i (List.mem_of_getElem? hpa)
      simp [List.getElem?_eq_getElem hi]

/-- Every sublist is the subword at some increasing list of positions. -/
theorem exists_picks_of_sublist (h : s <+ w) : ∃ ps, Picks w ps s := by
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_orderEmbedding_getElem?_eq.mp h
  refine ⟨(List.range s.length).map f, ?_, ?_, by simp, ?_⟩
  · rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp (fun hab => f.strictMono hab)
  · intro i hi
    simp only [List.mem_map, List.mem_range] at hi
    obtain ⟨a, ha, rfl⟩ := hi
    have hfa := hf a
    rw [List.getElem?_eq_getElem ha] at hfa
    obtain ⟨h', -⟩ := List.getElem?_eq_some_iff.mp hfa.symm
    exact h'
  · intro a
    by_cases ha : a < s.length
    · rw [List.getElem?_map, List.getElem?_range ha]
      simpa using hf a
    · rw [List.getElem?_eq_none (by omega), List.getElem?_map,
        List.getElem?_eq_none (by simpa using Nat.le_of_not_lt ha)]
      rfl

/-! ### Subwords confined to a prefix or to a suffix

`Picks` records the positions at which a subword is read off, so it is the natural tool for
saying that a subword lies entirely before, or entirely after, a given position. -/

/-- A subword whose positions all lie before `m` is a subword of the prefix `w.take m`. -/
theorem Picks.take (h : Picks w ps s) (hlt : ∀ i ∈ ps, i < m) : Picks (w.take m) ps s where
  incr := h.incr
  range := by
    intro i hi
    have h1 := h.range i hi
    have h2 := hlt i hi
    simp only [List.length_take]
    omega
  length := h.length
  val := by
    intro a
    rw [h.val a]
    cases hpa : ps[a]? with
    | none => simp
    | some i =>
      have hi : i < m := hlt i (List.mem_of_getElem? hpa)
      simp [List.getElem?_take_of_lt hi]

/-- A subword whose positions all lie at or after `m` is a subword of the suffix `w.drop m`,
read off at the positions shifted down by `m`. -/
theorem Picks.drop (h : Picks w ps s) (hge : ∀ i ∈ ps, m ≤ i) :
    Picks (w.drop m) (ps.map (fun i => i - m)) s where
  incr := by
    rw [List.pairwise_map]
    refine h.incr.imp_of_mem ?_
    intro a b ha hb hab
    have := hge a ha
    omega
  range := by
    intro i hi
    simp only [List.mem_map] at hi
    obtain ⟨a, ha, rfl⟩ := hi
    have h1 := h.range a ha
    have h2 := hge a ha
    simp only [List.length_drop]
    omega
  length := by rw [h.length, List.length_map]
  val := by
    intro a
    rw [h.val a, List.getElem?_map]
    cases hpa : ps[a]? with
    | none => simp
    | some i =>
      have hi : m ≤ i := hge i (List.mem_of_getElem? hpa)
      simp only [Option.map_some, Option.bind_some, List.getElem?_drop]
      congr 1
      omega

/-- The three letters of `w` at increasing positions `i < j < k` form a subword. -/
theorem triple_sublist {i j k : ℕ} (hi : i < w.length) (hj : j < w.length)
    (hk : k < w.length) (hij : i < j) (hjk : j < k) : [w[i], w[j], w[k]] <+ w := by
  have hrange : ∀ a ∈ ([i, j, k] : List ℕ), a < w.length := by
    intro a ha; fin_cases ha <;> assumption
  have hpick := picks_map (w := w) (pairwise_triple_iff.mpr ⟨hij, hjk⟩) hrange
  have hmap : ([i, j, k] : List ℕ).map (fun a => w.getD a 0) = [w[i], w[j], w[k]] := by
    simp only [List.map_cons, List.map_nil, List.getD_eq_getElem _ _ hi,
      List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hk]
  rw [hmap] at hpick
  exact hpick.sublist

end PermPatterns
