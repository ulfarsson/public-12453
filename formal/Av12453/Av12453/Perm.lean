/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
module

public import PermPatterns.Perm
public import Av12453.OneThreshold.KernelCount
public import Av12453.TwoThreshold.KernelCount
meta import PermPatterns.Perm
meta import Av12453.OneThreshold.KernelCount
meta import Av12453.TwoThreshold.KernelCount

@[expose] public section

/-!
# The headline counts, restated for Mathlib's `Equiv.Perm (Fin n)`

The two kernel algorithms are proved correct against `PermPatterns.avoiders`, a `Finset` of
words.  This file restates their conclusions on Mathlib's model of a permutation, an element
of `Equiv.Perm (Fin n)`, using the bridge of `PermPatterns.Perm`.  Nothing here is used by
the development; it is the interface a Mathlib reader expects.

## Main definitions

* `Av12453.beta1Perm`, `Av12453.beta2Perm` : the patterns `β_1 = 1342` and `β_2 = 12453` as
  elements of `Equiv.Perm (Fin 4)` and `Equiv.Perm (Fin 5)`.

## Main results

* `Av12453.OneThreshold.av1342_count_perm` : `G_n` is the number of permutations of `Fin n`
  avoiding `β_1 = 1342`.
* `Av12453.TwoThreshold.av12453_count_perm` : `G_{(n,0)}` is the number of permutations of
  `Fin n` avoiding `β_2 = 12453`.
-/

namespace Av12453

open PermPatterns

/-- The pattern `β_1 = 1342` as a permutation of `Fin 4`. -/
def beta1Perm : Equiv.Perm (Fin 4) := toPerm (beta 1) (by decide)

/-- The pattern `β_2 = 12453` as a permutation of `Fin 5`. -/
def beta2Perm : Equiv.Perm (Fin 5) := toPerm (beta 2) (by decide)

/-- The word of `beta1Perm` is `β_1 = 1342`. -/
@[simp] theorem ofPerm_beta1Perm : ofPerm beta1Perm = beta 1 := ofPerm_toPerm _ _

/-- The word of `beta2Perm` is `β_2 = 12453`. -/
@[simp] theorem ofPerm_beta2Perm : ofPerm beta2Perm = beta 2 := ofPerm_toPerm _ _

namespace OneThreshold

/--
**`|Av_n(1342)|` by the kernel algorithm, on `Equiv.Perm (Fin n)`**: the number `G n`
computed from the scalar kernel table is the number of permutations of `Fin n` avoiding
`β_1 = 1342`.  This is
`Av12453.OneThreshold.av1342_count_kernel` read through
`PermPatterns.card_avoiders_singleton_eq_fintypeCard`.
-/
theorem av1342_count_perm (n : ℕ) :
    G n = Fintype.card {σ : Equiv.Perm (Fin n) // PermAvoids σ beta1Perm} := by
  rw [av1342_count_kernel n, ← ofPerm_beta1Perm, card_avoiders_singleton_eq_fintypeCard]

end OneThreshold

namespace TwoThreshold

/--
**`|Av_n(12453)|` by the kernel algorithm, on `Equiv.Perm (Fin n)`**: the number
`G (n, 0)` computed from the two-threshold kernel table is the number of permutations of
`Fin n` avoiding
`β_2 = 12453`.  This is `Av12453.TwoThreshold.av12453_count_kernel` read through
`PermPatterns.card_avoiders_singleton_eq_fintypeCard`.
-/
theorem av12453_count_perm (n : ℕ) :
    G (n, 0) = Fintype.card {σ : Equiv.Perm (Fin n) // PermAvoids σ beta2Perm} := by
  rw [av12453_count_kernel n, ← ofPerm_beta2Perm, card_avoiders_singleton_eq_fintypeCard]

end TwoThreshold

/-! ### Sanity checks

The two counts evaluated directly on `Equiv.Perm (Fin n)` for small `n`, and compared with
the kernel algorithms. -/

/-- The word of `beta1Perm` is `β_1 = 1342`, `0`-based. -/
example : ofPerm beta1Perm = [0, 2, 3, 1] := by decide

/-- The word of `beta2Perm` is `β_2 = 12453`, `0`-based. -/
example : ofPerm beta2Perm = [0, 1, 3, 4, 2] := by decide

set_option linter.hashCommand false in
/-- info: [1, 1, 2, 6, 23] -/
#guard_msgs in
#eval (List.range 5).map fun n =>
  Fintype.card {σ : Equiv.Perm (Fin n) // PermAvoids σ beta1Perm}

set_option linter.hashCommand false in
/-- info: [1, 1, 2, 6, 24, 119] -/
#guard_msgs in
#eval (List.range 6).map fun n =>
  Fintype.card {σ : Equiv.Perm (Fin n) // PermAvoids σ beta2Perm}

set_option linter.hashCommand false in
/-- info: [true, true, true, true, true] -/
#guard_msgs in
#eval (List.range 5).map fun n =>
  OneThreshold.G n == Fintype.card {σ : Equiv.Perm (Fin n) // PermAvoids σ beta1Perm}

set_option linter.hashCommand false in
/-- info: [true, true, true, true, true, true] -/
#guard_msgs in
#eval (List.range 6).map fun n =>
  TwoThreshold.G (n, 0) == Fintype.card {σ : Equiv.Perm (Fin n) // PermAvoids σ beta2Perm}

end Av12453
