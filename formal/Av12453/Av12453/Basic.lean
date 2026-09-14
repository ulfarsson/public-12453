/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Mathlib

/-!
# Words, patterns and containment

This file sets up the pattern-avoidance apparatus used in Section 2 of the paper
*Protected tails and polynomial-time enumeration of permutations avoiding a direct sum of an
increasing pattern and 231*.

## Translation table: the paper's notation and this development's

The paper numbers values and positions from `1`; **this development numbers both from `0`**,
matching Mathlib's `Fin n` and `List.range n` and the `permuta` library.  Only the labels
differ: every notion below is a statement about the *relative order* of letters, which the
two conventions describe equally well (`Av12453.contains_congr_word`).

| paper | Lean |
|---|---|
| values `1, 2, …, n` | values `0, 1, …, n-1`; `IsPermOf n w` is `w.Perm (List.range n)` |
| positions `1, …, n`; the letter `π_j` | positions `0, …, n-1`; the paper's position `j` is the
  index `j - 1`; Lean quantifies over the 0-based index directly and writes the letter `w[j]` |
| the suffix after position `j`, `π_{j+1} ⋯ π_n` | `w.drop (j + 1)` after the 0-based index `j`
  (this is `w.drop j` in terms of the paper's 1-based `j`) |
| `ι_d = 12⋯d` | `iota d = List.range d = [0, 1, …, d-1]` |
| the pattern `231` | `pat231 = [1, 2, 0]` |
| `β_d = ι_d ⊕ 231` | `beta d = iota d ++ [d + 1, d + 2, d]` |
| `β_1 = 1342` | `beta 1 = [0, 2, 3, 1]` (`Av12453.beta_one`, by `decide`) |
| `β_2 = 12453` | `beta 2 = [0, 1, 3, 4, 2]` (`Av12453.beta_two`, by `decide`) |
| the standardization `st(w)` | `standardize w`, the rank map, with values `0, …, k-1` |
| the restriction `w\|_X` | `restrict w X`, definitionally a `List.filter` |
| local rank `r`, the number of values `≤ x` | `rank x w + 1`; `rank x w` counts the values `< x` |

## Modelling decisions

* A **word** is a `List ℕ`.  The paper's words have *distinct entries*; this is recorded as
  an explicit `List.Nodup` hypothesis wherever it is needed.  Modelling the paper's "finite
  totally ordered set `I`" by a set of natural numbers is no loss of generality: every
  finite totally ordered set is order-isomorphic to a finite set of naturals, and every
  notion below is invariant under order isomorphism (`Av12453.contains_congr_word`).
* Two words are **order-isomorphic** (`Av12453.OrderIso`) when they have the same length and
  the same relative order at every pair of positions.  This is the relation the paper writes
  as `st u = st v`: a word with distinct entries is order-isomorphic to its standardization
  (`Av12453.orderIso_standardize`), so the two readings agree.
* A word **contains** a pattern when some subsequence (`List.Sublist`; the positions need
  not be adjacent) is order-isomorphic to the pattern.  **Avoidance** is the negation.
  Containment is invariant under order isomorphism on both sides
  (`Av12453.contains_congr_word`, `Av12453.contains_congr_pattern`), so the paper's phrase
  "avoids `231` after standardization" can be read either as `Avoids _ pat231` or literally
  as `Avoids (standardize _) pat231`; the two are equivalent
  (`Av12453.avoids_standardize_iff`).
* The restriction `w\|_X` of the paper is `List.filter`.

## Main definitions

* `Av12453.OrderIso`, `Av12453.Contains`, `Av12453.Avoids`.
* `Av12453.Picks w ps s` : `s` is the subword of `w` read off at the strictly increasing
  list of positions `ps`.  This is the index-level description of `s <+ w`.
* `Av12453.restrict` : the paper's `w\|_X`.
* `Av12453.rank`, `Av12453.standardize` : the `0`-based local rank and the paper's `st(w)`.
* `Av12453.card_filter_le_eq_rank_succ` : the paper's local rank `r = |{y ∈ I : y ≤ x}|`
  equals `rank x w + 1`.
* `Av12453.pat231`, `Av12453.iota`, `Av12453.beta` : the patterns `231`, `ι_d = 12⋯d` and
  `β_d = ι_d ⊕ 231`, written `0`-based as in the table above.
* `Av12453.IncrSubseq`, `Av12453.IsTriggerAt`, `Av12453.IsTrigger` : increasing
  `d`-subsequences and `d`-triggers.

## Main results

* `Av12453.orderIso_equivalence` : order isomorphism is an equivalence relation.
* `Av12453.Contains.of_sublist`, `Av12453.Avoids.sublist` : monotonicity of containment
  under sublists.
* `Av12453.contains_congr_word` : containment depends only on the order type of the word.
* `Av12453.orderIso_standardize`, `Av12453.standardize_nodup`,
  `Av12453.standardize_isPermOf`, `Av12453.contains_standardize_iff`,
  `Av12453.avoids_standardize_iff` : standardization and its invariance properties.
* `Av12453.contains_231_iff` : `w` contains `231` iff there are positions `i < j < k` with
  `w[k] < w[i] < w[j]`.
* `Av12453.contains_beta_iff` : `w` contains `β_d` iff there are positions
  `i₁ < ⋯ < i_d < j < k < l` with `w[i₁] < ⋯ < w[i_d] < w[l] < w[j] < w[k]`.
* `Av12453.restrict_sublist`, `Av12453.restrict_nodup` : `w\|_X <+ w`, and `w\|_X` has
  distinct entries when `w` does.

Lists of positions are required to be `List.Pairwise (· < ·)`, which by
`List.isChain_iff_pairwise` is the same as the chain `i₁ < i₂ < ⋯` of the paper.  Letters
are written `w.getD i 0`; whenever `i < w.length` this is `w[i]` (`List.getD_eq_getElem`),
and every statement below carries the corresponding range hypothesis.
-/

namespace Av12453

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

/-! ### Order isomorphism -/

/--
Two words are *order-isomorphic* when they have the same length and, at every pair of
positions, their entries compare in the same way.  Equivalently, they have the same
standardization.
-/
def OrderIso (u v : List ℕ) : Prop :=
  u.length = v.length ∧
    ∀ (i j : ℕ) (_hiu : i < u.length) (_hju : j < u.length)
      (_hiv : i < v.length) (_hjv : j < v.length), u[i] < u[j] ↔ v[i] < v[j]

theorem OrderIso.length_eq (h : OrderIso u v) : u.length = v.length := h.1

theorem OrderIso.lt_iff (h : OrderIso u v) {i j : ℕ} (hiu : i < u.length) (hju : j < u.length)
    (hiv : i < v.length) (hjv : j < v.length) : u[i] < u[j] ↔ v[i] < v[j] :=
  h.2 i j hiu hju hiv hjv

@[refl]
theorem OrderIso.refl (u : List ℕ) : OrderIso u u := ⟨rfl, fun _ _ _ _ _ _ => Iff.rfl⟩

theorem OrderIso.symm (h : OrderIso u v) : OrderIso v u :=
  ⟨h.1.symm, fun i j hiv hjv hiu hju => (h.2 i j hiu hju hiv hjv).symm⟩

theorem OrderIso.trans (h₁ : OrderIso u v) (h₂ : OrderIso v w) : OrderIso u w := by
  obtain ⟨hl₁, hr₁⟩ := h₁
  obtain ⟨hl₂, hr₂⟩ := h₂
  refine ⟨hl₁.trans hl₂, fun i j hiu hju hiw hjw => ?_⟩
  have hiv : i < v.length := by omega
  have hjv : j < v.length := by omega
  exact (hr₁ i j hiu hju hiv hjv).trans (hr₂ i j hiv hjv hiw hjw)

/-- Order isomorphism of words is an equivalence relation. -/
theorem orderIso_equivalence : Equivalence OrderIso :=
  ⟨OrderIso.refl, OrderIso.symm, OrderIso.trans⟩

/-- Order-isomorphic words have distinct entries simultaneously. -/
theorem OrderIso.nodup (h : OrderIso u v) (hu : u.Nodup) : v.Nodup := by
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

/-- The direct sum of order isomorphisms: if `u₁` sits below `u₂` and `v₁` below `v₂`, then
order isomorphisms of the halves assemble.  This is the paper's `⊕`. -/
theorem OrderIso.append {u₁ u₂ v₁ v₂ : List ℕ} (h₁ : OrderIso u₁ v₁) (h₂ : OrderIso u₂ v₂)
    (hu : ∀ x ∈ u₁, ∀ y ∈ u₂, x < y) (hv : ∀ x ∈ v₁, ∀ y ∈ v₂, x < y) :
    OrderIso (u₁ ++ u₂) (v₁ ++ v₂) := by
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
theorem OrderIso.exists_append {v₁ v₂ : List ℕ} (hv : ∀ x ∈ v₁, ∀ y ∈ v₂, x < y)
    (h : OrderIso s (v₁ ++ v₂)) :
    ∃ u₁ u₂, s = u₁ ++ u₂ ∧ u₁.length = v₁.length ∧ OrderIso u₁ v₁ ∧ OrderIso u₂ v₂ ∧
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

/-! ### Containment and avoidance -/

/--
`Contains w τ` : the word `w` contains the pattern `τ`, i.e. some subsequence of `w`
(a `List.Sublist`; the positions need not be adjacent) is order-isomorphic to `τ`.
-/
def Contains (w τ : List ℕ) : Prop := ∃ s, s <+ w ∧ OrderIso s τ

/-- `Avoids w τ` : the word `w` avoids the pattern `τ`. -/
def Avoids (w τ : List ℕ) : Prop := ¬ Contains w τ

theorem avoids_iff : Avoids w τ ↔ ¬ Contains w τ := Iff.rfl

/-- Containment stated at the level of positions. -/
theorem contains_iff_picks : Contains w τ ↔ ∃ ps s, Picks w ps s ∧ OrderIso s τ := by
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
theorem contains_congr_pattern (h : OrderIso τ τ') : Contains w τ ↔ Contains w τ' :=
  ⟨fun ⟨s, hs, hiso⟩ => ⟨s, hs, hiso.trans h⟩, fun ⟨s, hs, hiso⟩ => ⟨s, hs, hiso.trans h.symm⟩⟩

/-- Containment depends only on the order type of the word; this is why standardization
never has to be mentioned. -/
theorem contains_congr_word (h : OrderIso w v) : Contains w τ ↔ Contains v τ := by
  have key : ∀ {w v : List ℕ}, OrderIso w v → Contains w τ → Contains v τ := by
    rintro w v h ⟨s, hs, hiso⟩
    obtain ⟨ps, hp⟩ := exists_picks_of_sublist hs
    have hrange : ∀ i ∈ ps, i < v.length := fun i hi => h.length_eq ▸ hp.range i hi
    have hq : Picks v ps (ps.map (fun i => v.getD i 0)) := picks_map hp.incr hrange
    refine ⟨ps.map (fun i => v.getD i 0), hq.sublist, OrderIso.trans ?_ hiso⟩
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
theorem avoids_congr_word (h : OrderIso w v) : Avoids w τ ↔ Avoids v τ :=
  not_congr (contains_congr_word h)

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
    Avoids (Av12453.restrict w X) τ :=
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

/-! ### Local rank and standardization -/

/--
The *local rank* of `x` in the word `x :: w`, counted `0`-based: the number of letters
strictly below `x`.  The paper's local rank is `r = |{y ∈ I : y ≤ x}|`, and since `x` itself
is counted there, `r = rank x w + 1`.
-/
def rank (x : ℕ) (w : List ℕ) : ℕ := ((x :: w).filter (· < x)).length

/-- `x` does not count towards its own rank, so the rank is computed in the tail. -/
theorem rank_eq_length_filter : rank x w = (w.filter (· < x)).length := by
  rw [rank, List.filter_cons_of_neg (by simp)]

/-- The local rank as a cardinality: for a word with distinct entries, `rank x w` is the
number of values of the underlying set `I` that are strictly below `x`, i.e. the paper's
`r - 1`. -/
theorem rank_eq_card (hnd : (x :: w).Nodup) :
    rank x w = ((x :: w).toFinset.filter (fun y => y < x)).card := by
  rw [rank, ← List.toFinset_card_of_nodup (hnd.filter _)]
  refine congrArg Finset.card (Finset.ext fun a => ?_)
  constructor
  · intro ha
    have h := List.mem_filter.mp (List.mem_toFinset.mp ha)
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr h.1, by simpa using h.2⟩
  · intro ha
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp ha
    exact List.mem_toFinset.mpr
      (List.mem_filter.mpr ⟨List.mem_toFinset.mp h1, by simpa using h2⟩)

/--
**The paper's local rank.**  For a word with distinct entries, the number of values of
`I = {x} ∪ w` that are `≤ x` — the paper's `r = |{y ∈ I : y ≤ x}|` — is `rank x w + 1`,
because `x` itself is counted on the left and not on the right.  This is the bridge between
the paper's `1`-based local rank and the `0`-based `Av12453.rank` used here.
-/
theorem card_filter_le_eq_rank_succ (hnd : (x :: w).Nodup) :
    ((x :: w).toFinset.filter (fun y => y ≤ x)).card = rank x w + 1 := by
  have hx : x ∉ w := (List.nodup_cons.mp hnd).1
  have hcard : ((x :: w).toFinset.filter (fun y => y ≤ x)).card
      = ((x :: w).filter (fun y => y ≤ x)).length := by
    rw [← List.toFinset_card_of_nodup (hnd.filter _), List.toFinset_filter]
    simp
  have hlow : ((x :: w).filter (fun y => y ≤ x)) = x :: w.filter (· < x) := by
    rw [List.filter_cons_of_pos (by simp)]
    congr 1
    refine List.filter_congr fun a ha => ?_
    have : a ≠ x := fun he => hx (he ▸ ha)
    simp only [decide_eq_decide]
    omega
  rw [hcard, hlow, List.length_cons, rank_eq_length_filter]

/-- The number of letters of `w` below a threshold, as a cardinality. -/
theorem length_filter_lt_eq_card (hnd : w.Nodup) (z : ℕ) :
    (w.filter (· < z)).length = (w.toFinset.filter (fun a => a < z)).card := by
  rw [← List.toFinset_card_of_nodup (hnd.filter _)]
  exact congrArg Finset.card (Finset.ext fun a => by simp)

/-- The rank map `x ↦ |{y ∈ w : y < x}|` is monotone. -/
theorem length_filter_lt_mono (hnd : w.Nodup) (hxy : x ≤ y) :
    (w.filter (· < x)).length ≤ (w.filter (· < y)).length := by
  rw [length_filter_lt_eq_card hnd, length_filter_lt_eq_card hnd]
  refine Finset.card_le_card fun a ha => ?_
  simp only [Finset.mem_filter] at ha ⊢
  exact ⟨ha.1, lt_of_lt_of_le ha.2 hxy⟩

/-- The rank map is strictly monotone at the letters of a word with distinct entries. -/
theorem length_filter_lt_strictMono (hnd : w.Nodup) (hx : x ∈ w) (hxy : x < y) :
    (w.filter (· < x)).length < (w.filter (· < y)).length := by
  rw [length_filter_lt_eq_card hnd, length_filter_lt_eq_card hnd]
  have hsub : w.toFinset.filter (fun a => a < x) ⊆ w.toFinset.filter (fun a => a < y) := by
    intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, ha.2.trans hxy⟩
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨x, ?_, ?_⟩)
  · simp [List.mem_toFinset, hx, hxy]
  · simp

/-- **The rank map reflects and preserves the order.**  For a word with distinct entries and
a letter `x` of it, `x < y` holds exactly when `x` has the smaller rank. -/
theorem lt_iff_length_filter_lt (hnd : w.Nodup) (hx : x ∈ w) :
    x < y ↔ (w.filter (· < x)).length < (w.filter (· < y)).length := by
  refine ⟨length_filter_lt_strictMono hnd hx, fun h => ?_⟩
  by_contra hxy
  exact absurd (length_filter_lt_mono hnd (Nat.le_of_not_lt hxy)) (Nat.not_le.mpr h)

/-- Every rank is smaller than the length of the word: a letter of `w` is not below
itself, so the lower block is a proper part of `w`. -/
theorem length_filter_lt_length_of_mem (hnd : w.Nodup) (hx : x ∈ w) :
    (w.filter (· < x)).length < w.length := by
  rw [length_filter_lt_eq_card hnd, ← List.toFinset_card_of_nodup hnd]
  have hsub : w.toFinset.filter (fun a => a < x) ⊆ w.toFinset := fun a ha =>
    (Finset.mem_filter.mp ha).1
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨x, ?_, ?_⟩)
  · simpa using hx
  · simp

/--
The paper's *standardization* `st(w)`: every letter is replaced by its rank, so a word with
`k` distinct letters becomes a word on the values `0, 1, …, k-1` with the same relative
order.  (The paper replaces the smallest entry by `1`; here values are `0`-based, so the
smallest entry becomes `0`.)
-/
def standardize (w : List ℕ) : List ℕ := w.map (fun x => (w.filter (· < x)).length)

@[simp] theorem length_standardize : (standardize w).length = w.length := by
  simp [standardize]

/-- The `i`-th letter of `standardize w` is the rank of the `i`-th letter of `w`. -/
theorem getElem_standardize {i : ℕ} (hi : i < (standardize w).length) :
    (standardize w)[i] = (w.filter (· < w[i]'(by simpa using hi))).length := by
  simp only [standardize, List.getElem_map]

/-- **Standardization preserves the order type**: a word with distinct entries is
order-isomorphic to its standardization.  This is the precise form of the paper's `st(w)`
and the reason "avoids `231` after standardization" may be read without `st`. -/
theorem orderIso_standardize (hnd : w.Nodup) : OrderIso w (standardize w) := by
  refine ⟨by simp, fun i j hiu hju hiv hjv => ?_⟩
  rw [getElem_standardize hiv, getElem_standardize hjv]
  exact lt_iff_length_filter_lt hnd (List.getElem_mem hiu)

/-- The standardization of a word with distinct entries again has distinct entries. -/
theorem standardize_nodup (hnd : w.Nodup) : (standardize w).Nodup :=
  (orderIso_standardize hnd).nodup hnd

/-- The standardization of a word with `n` distinct letters is a permutation of
`{0, 1, …, n-1}`. -/
theorem standardize_isPermOf (hnd : w.Nodup) : IsPermOf w.length (standardize w) := by
  refine List.perm_of_nodup_nodup_toFinset_eq (standardize_nodup hnd) List.nodup_range ?_
  refine Finset.eq_of_subset_of_card_le (fun a ha => ?_) ?_
  · simp only [List.mem_toFinset, List.mem_range, standardize, List.mem_map] at ha ⊢
    obtain ⟨z, hz, rfl⟩ := ha
    exact length_filter_lt_length_of_mem hnd hz
  · rw [List.toFinset_card_of_nodup (standardize_nodup hnd),
      List.toFinset_card_of_nodup List.nodup_range]
    simp

/-- **Containment is unaffected by standardization.**  This is the bridge from the paper's
"after standardization" to the `OrderIso`-based definition used here. -/
theorem contains_standardize_iff (hnd : w.Nodup) : Contains (standardize w) τ ↔ Contains w τ :=
  (contains_congr_word (orderIso_standardize hnd)).symm

/-- **Avoidance is unaffected by standardization.** -/
theorem avoids_standardize_iff (hnd : w.Nodup) : Avoids (standardize w) τ ↔ Avoids w τ :=
  not_congr (contains_standardize_iff hnd)

/-! ### The patterns `231`, `ι_d` and `β_d` -/

/-- The pattern `231`, written `0`-based. -/
def pat231 : List ℕ := [1, 2, 0]

/-- The increasing pattern `ι_d = 12⋯d`, written `0`-based as `0, 1, …, d-1`. -/
def iota (d : ℕ) : List ℕ := List.range d

/-- The pattern `β_d = ι_d ⊕ 231`, written `0`-based as `0, 1, …, d-1, d+1, d+2, d`. -/
def beta (d : ℕ) : List ℕ := iota d ++ [d + 1, d + 2, d]

@[simp] theorem length_iota (d : ℕ) : (iota d).length = d := by simp [iota]

@[simp] theorem length_beta (d : ℕ) : (beta d).length = d + 3 := by simp [beta]

/-- `β_1` is the paper's `1342`, written `0`-based. -/
theorem beta_one : beta 1 = [0, 2, 3, 1] := by decide

/-- `β_2` is the paper's `12453`, written `0`-based. -/
theorem beta_two : beta 2 = [0, 1, 3, 4, 2] := by decide

theorem getElem_iota {d a : ℕ} (h : a < (iota d).length) : (iota d)[a] = a := by
  simp [iota]

theorem mem_iota_lt {d z : ℕ} (h : z ∈ iota d) : z < d := by
  simpa [iota] using h

/-- The direct-sum shape of `β_d`: every entry of `ι_d` is below the last three entries. -/
theorem beta_lt {d : ℕ} : ∀ x ∈ iota d, ∀ y ∈ [d + 1, d + 2, d], x < y := by
  intro x hx y hy
  have := mem_iota_lt hx
  fin_cases hy <;> omega

/-! ### Order isomorphism with the concrete patterns -/

/-- A word is order-isomorphic to `ι_d` exactly when it is a strictly increasing word of
length `d`. -/
theorem orderIso_iota_iff {d : ℕ} : OrderIso u (iota d) ↔ u.length = d ∧ u.Pairwise (· < ·) := by
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
theorem orderIso_triple_iff {p q r x y z : ℕ} (hzx : z < x) (hxy : x < y) :
    OrderIso [p, q, r] [x, y, z] ↔ r < p ∧ p < q := by
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
    obtain ⟨h1, h2⟩ := (orderIso_triple_iff (p := w[i]) (q := w[j]) (r := w[k]) (x := 1) (y := 2)
      (z := 0) (by norm_num) (by norm_num)).mp hiso
    exact ⟨i, j, k, hi, hj, hk, hij, hjk, h1, h2⟩
  · rintro ⟨i, j, k, hi, hj, hk, hij, hjk, h1, h2⟩
    exact ⟨[w[i], w[j], w[k]], triple_sublist hi hj hk hij hjk,
      (orderIso_triple_iff (x := 1) (y := 2) (z := 0) (by norm_num) (by norm_num)).mpr
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
    obtain ⟨hlj, hjk⟩ := (orderIso_triple_iff (x := d + 1) (y := d + 2) (z := d)
      (by omega) (by omega)).mp hiso₂
    refine ⟨qs.take d, j, k, l, htakelen,
      fun i hi => hrange i (by rw [hqs]; exact List.mem_append_left _ hi), hjr, hkr, hlr, ?_, ?_⟩
    · rw [← hqs]; exact hp.incr
    · rw [List.pairwise_append]
      refine ⟨by rw [← hu₁]; exact (orderIso_iota_iff.mp hiso₁).2,
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
      refine (orderIso_iota_iff.mpr ⟨by simp [hlen], hval₁⟩).append ?_ ?_ beta_lt
      · simp only [List.map_cons, List.map_nil]
        exact (orderIso_triple_iff (x := d + 1) (y := d + 2) (z := d) (by omega)
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

/-- The paper's `β_2 = 12453` occurs in the word `12453` (`0`-based: `[0, 1, 3, 4, 2]`). -/
example : Contains [0, 1, 3, 4, 2] (beta 2) :=
  ⟨[0, 1, 3, 4, 2], List.Sublist.refl _, beta_two ▸ OrderIso.refl _⟩

/-- Standardization on a concrete word: the ranks of `9, 4, 7` are `2, 0, 1`. -/
example : standardize [9, 4, 7] = [2, 0, 1] := by decide

/-- The standardization of a word with distinct entries is a permutation of `{0, …, n-1}`. -/
example : IsPermOf 3 (standardize [9, 4, 7]) := standardize_isPermOf (by decide)

end Av12453
