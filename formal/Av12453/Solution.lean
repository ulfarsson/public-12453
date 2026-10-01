module

public import Av12453

@[expose] public section

/-!
# Polynomial-time enumeration of `Av(1342)` and `Av(12453)`: the proofs

The four theorems of `Challenge.lean`, proved from the development in `PermPatterns/` and
`Av12453/`.  The definitions of `Challenge.lean` are those of the development, except the
two patterns, which `Challenge.lean` writes as products of transpositions; they are
defined identically here and identified with the development's `beta1Perm` and
`beta2Perm` by `decide`.
-/

namespace Av12453

/-- The pattern `1342` as a permutation of `Fin 4` (`0`-based one-line notation `0 2 3 1`). -/
def pattern1342 : Equiv.Perm (Fin 4) := Equiv.swap 1 3 * Equiv.swap 1 2

/-- The pattern `12453` as a permutation of `Fin 5` (`0`-based one-line notation
`0 1 3 4 2`). -/
def pattern12453 : Equiv.Perm (Fin 5) := Equiv.swap 2 4 * Equiv.swap 2 3

theorem pattern1342_eq : pattern1342 = beta1Perm := by decide

theorem pattern12453_eq : pattern12453 = beta2Perm := by decide

private theorem natCard_eq {n k : ℕ} (τ : Equiv.Perm (Fin k)) :
    Nat.card {σ : Equiv.Perm (Fin n) // ¬ PermPatterns.PermContains σ τ} =
      Fintype.card {σ : Equiv.Perm (Fin n) // PermPatterns.PermAvoids σ τ} := by
  rw [Nat.card_eq_fintype_card]
  rfl

/-- **`|Av_n(1342)|` by the scalar kernel algorithm** (Theorem 2.19 of the paper). -/
theorem count_1342_kernel (n : ℕ) :
    OneThreshold.G n =
      Nat.card {σ : Equiv.Perm (Fin n) // ¬ PermPatterns.PermContains σ pattern1342} := by
  rw [natCard_eq, pattern1342_eq, OneThreshold.av1342_count_perm]

/-- **`|Av_n(1342)|` by the one-threshold recurrence** (Proposition 2.10 of the paper). -/
theorem count_1342_literal (n : ℕ) :
    OneThreshold.W n [] =
      Nat.card {σ : Equiv.Perm (Fin n) // ¬ PermPatterns.PermContains σ pattern1342} := by
  rw [← OneThreshold.G_eq_W, count_1342_kernel]

/-- **`|Av_n(12453)|` by the two-threshold kernel algorithm** (Theorem 1.1 and
eq:answer-G of the paper at `d = 2`). -/
theorem count_12453_kernel (n : ℕ) :
    TwoThreshold.G (n, 0) =
      Nat.card {σ : Equiv.Perm (Fin n) // ¬ PermPatterns.PermContains σ pattern12453} := by
  rw [natCard_eq, pattern12453_eq, TwoThreshold.av12453_count_perm]

/-- **`|Av_n(12453)|` by the literal two-threshold recurrence** (Theorem 4.3 of the paper
at `d = 2`). -/
theorem count_12453_literal (n : ℕ) :
    TwoThreshold.H (n, 0) [] =
      Nat.card {σ : Equiv.Perm (Fin n) // ¬ PermPatterns.PermContains σ pattern12453} := by
  rw [← TwoThreshold.G_eq_H, count_12453_kernel]

end Av12453
