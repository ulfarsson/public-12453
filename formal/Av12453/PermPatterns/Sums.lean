/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import PermPatterns.Patterns

/-!
# Direct and skew sums of words

The two classical ways of putting one word beside another: the *direct sum* `α ⊕ β` places
`β` above and after `α`, and the *skew sum* `α ⊖ β` places `α` above and before `β`.  Values
are `0`-based, so "above" is realized by adding the length of the other word; no infix
notation is introduced.

## Main definitions

* `PermPatterns.directSum` : `α ⊕ β`, the word `α` followed by `β` shifted above it.
* `PermPatterns.skewSum` : `α ⊖ β`, the word `α` shifted above `β` and followed by `β`.

## Main results

* `PermPatterns.directSum_nodup`, `PermPatterns.skewSum_nodup`,
  `PermPatterns.directSum_isPermOf`, `PermPatterns.skewSum_isPermOf` : a sum of permutations
  of `{0, …, r-1}` and `{0, …, s-1}` is a permutation of `{0, …, r+s-1}`.
* `PermPatterns.orderIsomorphic_directSum`, `PermPatterns.orderIsomorphic_skewSum` : both
  sums depend only on the order types of the summands.
* `PermPatterns.contains_directSum_left`, `PermPatterns.contains_directSum_right` and their
  skew analogues : both summands are patterns of the sum.
* `PermPatterns.reverse_directSum`, `PermPatterns.skewSum_eq_reverse` : reversal exchanges
  the two sums.
-/

namespace PermPatterns

variable {α β α' β' : List ℕ}

/-! ### The two sums -/

/--
The *direct sum* `α ⊕ β` : the word `α`, followed by `β` with every letter raised above all
of `α` by `α.length`.  With `α` a word on `{0, …, α.length - 1}` this is the usual direct
sum of permutations.
-/
def directSum (α β : List ℕ) : List ℕ := α ++ β.map (· + α.length)

/--
The *skew sum* `α ⊖ β` : the word `α` with every letter raised above all of `β` by
`β.length`, followed by `β`.  With `β` a word on `{0, …, β.length - 1}` this is the usual
skew sum of permutations.
-/
def skewSum (α β : List ℕ) : List ℕ := α.map (· + β.length) ++ β

/-- The length of `α ⊕ β` is the sum of the two lengths. -/
@[simp] theorem length_directSum : (directSum α β).length = α.length + β.length := by
  simp [directSum]

/-- The length of `α ⊖ β` is the sum of the two lengths. -/
@[simp] theorem length_skewSum : (skewSum α β).length = α.length + β.length := by
  simp [skewSum]

/-- The letters of a direct sum: those of `α`, and those of `β` raised by `α.length`. -/
@[simp] theorem mem_directSum {z : ℕ} :
    z ∈ directSum α β ↔ z ∈ α ∨ ∃ y ∈ β, y + α.length = z := by
  simp [directSum]

/-- The letters of a skew sum: those of `α` raised by `β.length`, and those of `β`. -/
@[simp] theorem mem_skewSum {z : ℕ} :
    z ∈ skewSum α β ↔ (∃ x ∈ α, x + β.length = z) ∨ z ∈ β := by
  simp [skewSum]

/-! ### Reversal

Reversing a word exchanges the two sums; this is the symmetry that makes every skew-sum
statement below a corollary of its direct-sum counterpart. -/

/-- Reversing a word exchanges the two sums: `(α ⊕ β)ʳ = βʳ ⊖ αʳ`. -/
theorem reverse_directSum : (directSum α β).reverse = skewSum β.reverse α.reverse := by
  simp [directSum, skewSum]

/-- The skew sum as the reverse of a direct sum: `α ⊖ β = (βʳ ⊕ αʳ)ʳ`. -/
theorem skewSum_eq_reverse : skewSum α β = (directSum β.reverse α.reverse).reverse := by
  rw [reverse_directSum]
  simp [skewSum]

/-! ### Distinct entries and permutations -/

/-- A direct sum of words with distinct entries again has distinct entries, provided the
lower summand `α` uses only values below `α.length`. -/
theorem directSum_nodup (hα : ∀ x ∈ α, x < α.length) (hαnd : α.Nodup) (hβnd : β.Nodup) :
    (directSum α β).Nodup := by
  refine hαnd.append (hβnd.map fun a b h => by omega) ?_
  intro z hz hz'
  simp only [List.mem_map] at hz'
  obtain ⟨b, -, rfl⟩ := hz'
  have := hα _ hz
  omega

/-- A skew sum of words with distinct entries again has distinct entries, provided the lower
summand `β` uses only values below `β.length`. -/
theorem skewSum_nodup (hβ : ∀ y ∈ β, y < β.length) (hαnd : α.Nodup) (hβnd : β.Nodup) :
    (skewSum α β).Nodup := by
  refine (hαnd.map fun a b h => by omega).append hβnd ?_
  intro z hz hz'
  simp only [List.mem_map] at hz
  obtain ⟨a, -, rfl⟩ := hz
  have := hβ _ hz'
  omega

/-- The direct sum of a permutation of `{0, …, r-1}` and one of `{0, …, s-1}` is a
permutation of `{0, …, r+s-1}`. -/
theorem directSum_isPermOf {r s : ℕ} (hα : IsPermOf r α) (hβ : IsPermOf s β) :
    IsPermOf (r + s) (directSum α β) := by
  have hlen : α.length = r := hα.length
  have hmap : ((List.range s).map (· + r)) = (List.range s).map (r + ·) :=
    List.map_congr_left fun x _ => Nat.add_comm x r
  have hperm : (directSum α β).Perm (List.range r ++ (List.range s).map (· + r)) := by
    rw [directSum, hlen]
    exact hα.append (hβ.map _)
  rw [IsPermOf, List.range_add]
  rw [hmap] at hperm
  exact hperm

/-- The skew sum of a permutation of `{0, …, r-1}` and one of `{0, …, s-1}` is a permutation
of `{0, …, r+s-1}`. -/
theorem skewSum_isPermOf {r s : ℕ} (hα : IsPermOf r α) (hβ : IsPermOf s β) :
    IsPermOf (r + s) (skewSum α β) := by
  have hlen : β.length = s := hβ.length
  have hmap : ((List.range r).map (· + s)) = (List.range r).map (s + ·) :=
    List.map_congr_left fun x _ => Nat.add_comm x s
  have hperm : (skewSum α β).Perm ((List.range r).map (· + s) ++ List.range s) := by
    rw [skewSum, hlen]
    exact (hα.map _).append hβ
  rw [IsPermOf, Nat.add_comm r s, List.range_add]
  rw [hmap] at hperm
  exact hperm.trans (List.perm_append_comm)

/-! ### Order isomorphism -/

/-- The direct sum depends only on the order types of its summands, provided both lower
summands use only values below their length. -/
theorem orderIsomorphic_directSum (hα : OrderIsomorphic α α') (hβ : OrderIsomorphic β β')
    (hv : ∀ x ∈ α, x < α.length) (hv' : ∀ x ∈ α', x < α'.length) :
    OrderIsomorphic (directSum α β) (directSum α' β') := by
  simp only [directSum]
  refine hα.append ((orderIsomorphic_map_add β α.length).symm.trans
    (hβ.trans (orderIsomorphic_map_add β' α'.length))) ?_ ?_
  · intro x hx y hy
    simp only [List.mem_map] at hy
    obtain ⟨b, -, rfl⟩ := hy
    have := hv x hx
    omega
  · intro x hx y hy
    simp only [List.mem_map] at hy
    obtain ⟨b, -, rfl⟩ := hy
    have := hv' x hx
    omega

/-- The skew sum depends only on the order types of its summands, provided both lower
summands use only values below their length.  This is the direct-sum statement read through
`PermPatterns.skewSum_eq_reverse`. -/
theorem orderIsomorphic_skewSum (hα : OrderIsomorphic α α') (hβ : OrderIsomorphic β β')
    (hv : ∀ y ∈ β, y < β.length) (hv' : ∀ y ∈ β', y < β'.length) :
    OrderIsomorphic (skewSum α β) (skewSum α' β') := by
  rw [skewSum_eq_reverse, skewSum_eq_reverse]
  refine (orderIsomorphic_directSum hβ.reverse hα.reverse ?_ ?_).reverse
  · intro x hx
    rw [List.length_reverse]
    exact hv x (List.mem_reverse.mp hx)
  · intro x hx
    rw [List.length_reverse]
    exact hv' x (List.mem_reverse.mp hx)

/-! ### Both summands are patterns of the sum -/

/-- The lower summand of a direct sum is a pattern of it. -/
theorem contains_directSum_left : Contains (directSum α β) α :=
  ⟨α, List.sublist_append_left .., OrderIsomorphic.refl α⟩

/-- The upper summand of a direct sum is a pattern of it. -/
theorem contains_directSum_right : Contains (directSum α β) β :=
  ⟨β.map (· + α.length), List.sublist_append_right ..,
    (orderIsomorphic_map_add β α.length).symm⟩

/-- The upper summand of a skew sum is a pattern of it. -/
theorem contains_skewSum_left : Contains (skewSum α β) α :=
  ⟨α.map (· + β.length), List.sublist_append_left .., (orderIsomorphic_map_add α β.length).symm⟩

/-- The lower summand of a skew sum is a pattern of it. -/
theorem contains_skewSum_right : Contains (skewSum α β) β :=
  ⟨β, List.sublist_append_right .., OrderIsomorphic.refl β⟩

/-! ### Sanity checks -/

/-- `1 ⊕ 231 = 1342`, `0`-based. -/
example : directSum [0] [1, 2, 0] = [0, 2, 3, 1] := by decide

/-- `1 ⊖ 1 = 21`, `0`-based. -/
example : skewSum [0] [0] = [1, 0] := by decide

/-- `ι_2 ⊕ 231 = 12453`, `0`-based. -/
example : directSum (iota 2) pat231 = [0, 1, 3, 4, 2] := by decide

end PermPatterns
