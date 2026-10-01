/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
module

public import Mathlib.Data.List.Permutation
public import PermPatterns.Decidable

@[expose] public section

/-!
# Permutations and pattern avoiders

The finite sets this library counts in: all permutations of `{0, …, n-1}`, written as words,
and the ones avoiding every pattern of a finite basis.

## Main definitions

* `PermPatterns.perms` : the permutations of `{0, …, n-1}`, written as words.
* `PermPatterns.avoiders` : the permutations of `{0, …, n-1}` lying in the class `Av(B)`.

## Main results

* `PermPatterns.mem_perms` : membership in `perms n` is being a permutation of `{0, …, n-1}`.
* `PermPatterns.mem_avoiders`, `PermPatterns.mem_avoiders_singleton` : membership in
  `avoiders n B`, and in the one-pattern case `B = {τ}`.
* `PermPatterns.avoiders_empty`, `PermPatterns.avoiders_anti` : the empty basis forbids
  nothing, and enlarging the basis shrinks the class.
-/

namespace PermPatterns

variable {n : ℕ} {w τ : List ℕ} {B B' : Finset (List ℕ)}

/-- The permutations of `{0, …, n-1}`, written as words. -/
def perms (n : ℕ) : Finset (List ℕ) := (List.range n).permutations.toFinset

@[simp] theorem mem_perms {w : List ℕ} : w ∈ perms n ↔ IsPermOf n w := by
  simp [perms, IsPermOf, List.mem_permutations]

/-- The permutations of `{0, …, n-1}` avoiding every pattern of the basis `B`: the class
`Av_n(B)`, written as a `Finset` of words. -/
def avoiders (n : ℕ) (B : Finset (List ℕ)) : Finset (List ℕ) :=
  (perms n).filter fun w => AvoidsAll w B

@[simp] theorem mem_avoiders : w ∈ avoiders n B ↔ IsPermOf n w ∧ AvoidsAll w B := by
  simp [avoiders]

/-- Membership in the one-pattern case `B = {τ}`. -/
theorem mem_avoiders_singleton : w ∈ avoiders n {τ} ↔ IsPermOf n w ∧ Avoids w τ := by
  simp

/-- The empty basis forbids nothing. -/
@[simp] theorem avoiders_empty (n : ℕ) : avoiders n ∅ = perms n := by
  ext w; simp

/-- Enlarging the basis shrinks the class. -/
theorem avoiders_anti (h : B ⊆ B') : avoiders n B' ⊆ avoiders n B := fun w hw => by
  rw [mem_avoiders] at hw ⊢
  exact ⟨hw.1, hw.2.mono h⟩

end PermPatterns
