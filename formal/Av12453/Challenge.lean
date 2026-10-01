module

public import Mathlib

@[expose] public section

/-!
# Polynomial-time enumeration of `Av(1342)` and `Av(12453)`: the statement

This file is the statement surface of the Lean development accompanying

  H. A. S. Úlfarsson, *Protected tails and polynomial-time enumeration of permutations
  avoiding a direct sum of an increasing pattern and 231*, arXiv:2609.15642.

It contains, besides Mathlib, only the definitions that the four headline theorems use:
pattern containment for permutations of `Fin n`, the two patterns `1342` and `12453`, and
the paper's recurrences.  Each recurrence is evaluated with an explicit amount of fuel (a
recursion bound larger than the measure that every step decreases), so the definitions
below are plain structural recursions.

* `W p L` is the one-threshold recurrence (eq:W, eq:W-boundary of the paper) for the class
  `Av(1342)`; its value at `(n, [])` is `|Av_n(1342)|` (Proposition 2.10).
* `OneThreshold.G p` is the scalar kernel algorithm (eq:scalar-K, eq:scalar-G) for the same
  class, built from the kernel table `OneThreshold.K` (Theorem 2.19).
* `H p L` is the literal two-threshold recurrence (eq:H) for `Av(12453)` (Theorem 4.3 at
  `d = 2`).
* `TwoThreshold.G p` is the kernel algorithm (eq:K, eq:G) for `Av(12453)`, built from the
  table `TwoThreshold.K` (Theorem 1.1 at `d = 2`).

In the recurrences the endpoint reads of the active head are written as a separate term
(`if ℓ = 0 then … else 2 * …`), which in the paper are the terms `a = 0` and `b = 0` of
the split sums, and the sums over controls are restricted to controls of mass at most that
of the source control, which the paper's support lemmas show loses nothing.  Values are
`0`-based throughout.
-/

namespace PermPatterns

/-- `PermContains σ τ`: the permutation `σ` of `Fin n` contains the pattern `τ` of `Fin k`,
that is, some order embedding `f` of the positions of `τ` into those of `σ` makes the
letters of `σ` compare exactly as the letters of `τ` do. -/
def PermContains {n k : ℕ} (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin k)) : Prop :=
  ∃ f : Fin k ↪o Fin n, ∀ i j, τ i < τ j ↔ σ (f i) < σ (f j)

end PermPatterns

namespace Av12453

/-- The pattern `1342` as a permutation of `Fin 4` (`0`-based one-line notation `0 2 3 1`). -/
def pattern1342 : Equiv.Perm (Fin 4) := Equiv.swap 1 3 * Equiv.swap 1 2

/-- The pattern `12453` as a permutation of `Fin 5` (`0`-based one-line notation
`0 1 3 4 2`). -/
def pattern12453 : Equiv.Perm (Fin 5) := Equiv.swap 2 4 * Equiv.swap 2 3

namespace OneThreshold

/-- Delete the zero entries of a list (the paper's `nz`). -/
def nz (L : List ℕ) : List ℕ := L.filter (fun a => decide (a ≠ 0))

/-- The one-threshold recurrence evaluated with fuel `k`, at control `q` and interval
sizes `L` (head first). -/
def Waux : ℕ → ℕ → List ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, q, [] => (if q = 0 then 1 else 0) + ∑ h ∈ Finset.range q, Waux k h (nz [q - 1 - h])
  | _ + 1, _, 0 :: _ => 0
  | k + 1, q, (ℓ + 1) :: L' =>
      (∑ h ∈ Finset.range q, Waux k h ((ℓ + 1 + q - 1 - h) :: L'))
        + (if ℓ = 0 then Waux k q L' else 2 * Waux k q (ℓ :: L'))
        + ∑ a ∈ Finset.Ico 1 ℓ, Waux k q (a :: (ℓ - a) :: L')

/-- The one-threshold recurrence `W_q(L)` of the paper. -/
def W (q : ℕ) (l : List ℕ) : ℕ := Waux (q + l.sum + 1) q l

/-- The scalar kernel `K_ℓ(p, t)` evaluated with fuel `k`. -/
def Kaux : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | _ + 1, 0, p, t => if p = t then 1 else 0
  | k + 1, ℓ + 1, p, t =>
      (∑ h ∈ Finset.range p, Kaux k (ℓ + 1 + p - 1 - h) h t)
        + (if ℓ = 0 then (if p = t then 1 else 0) else 2 * Kaux k ℓ p t)
        + ∑ a ∈ Finset.Ico 1 ℓ, ∑ u ∈ Finset.range (p + 1), Kaux k a p u * Kaux k (ℓ - a) u t

/-- The scalar transfer kernel `K_ℓ(p, t)` of the paper. -/
def K (ℓ p t : ℕ) : ℕ := Kaux (p + ℓ + 1) ℓ p t

/-- The empty-stack values `G_p` evaluated with fuel `k`. -/
def Gaux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, p =>
      (if p = 0 then 1 else 0)
        + ∑ h ∈ Finset.range p, ∑ t ∈ Finset.range (h + 1), K (p - 1 - h) h t * Gaux k t

/-- The empty-stack values `G_p` of the scalar kernel algorithm. -/
def G (p : ℕ) : ℕ := Gaux (p + 1) p

end OneThreshold

namespace TwoThreshold

open OneThreshold (nz)

/-- The literal two-threshold recurrence evaluated with fuel `k`, at control `q = (p₀, p₁)`
and interval sizes `L` (head first). -/
def Haux : ℕ → ℕ × ℕ → List ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, q, [] =>
      (if q = (0, 0) then 1 else 0)
        + (∑ h ∈ Finset.range q.1, Haux k (h, q.2 + q.1 - 1 - h) [])
        + ∑ h ∈ Finset.range q.2, Haux k (q.1, h) (nz [q.2 - 1 - h])
  | _ + 1, _, 0 :: _ => 0
  | k + 1, q, (ℓ + 1) :: L' =>
      (∑ h ∈ Finset.range q.1, Haux k (h, q.2 + q.1 - 1 - h) ((ℓ + 1) :: L'))
        + (∑ h ∈ Finset.range q.2, Haux k (q.1, h) ((ℓ + 1 + (q.2 - 1 - h)) :: L'))
        + (if ℓ = 0 then Haux k q L' else 2 * Haux k q (ℓ :: L'))
        + ∑ a ∈ Finset.Ico 1 ℓ, Haux k q (a :: (ℓ - a) :: L')

/-- The literal two-threshold recurrence `H_q(L)` of the paper at `d = 2`. -/
def H (q : ℕ × ℕ) (l : List ℕ) : ℕ := Haux (q.1 + q.2 + l.sum + 1) q l

/-- The controls `(u₀, u₁)` of mass at most `M`. -/
def ctrls (M : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter fun u => u.1 + u.2 ≤ M

/-- The controls of mass at most that of `p`. -/
def S (p : ℕ × ℕ) : Finset (ℕ × ℕ) := ctrls (p.1 + p.2)

/-- The two-threshold kernel `K_ℓ(p, t)` evaluated with fuel `k`. -/
def Kaux : ℕ → ℕ → ℕ × ℕ → ℕ × ℕ → ℕ
  | 0, _, _, _ => 0
  | _ + 1, 0, p, t => if p = t then 1 else 0
  | k + 1, ℓ + 1, p, t =>
      (∑ h ∈ Finset.range p.1, Kaux k (ℓ + 1) (h, p.2 + p.1 - 1 - h) t)
        + (∑ h ∈ Finset.range p.2, Kaux k (ℓ + 1 + (p.2 - 1 - h)) (p.1, h) t)
        + (if ℓ = 0 then (if p = t then 1 else 0) else 2 * Kaux k ℓ p t)
        + ∑ a ∈ Finset.Ico 1 ℓ, ∑ u ∈ S p, Kaux k a p u * Kaux k (ℓ - a) u t

/-- The two-threshold transfer kernel `K_ℓ(p, t)` of the paper. -/
def K (ℓ : ℕ) (p t : ℕ × ℕ) : ℕ := Kaux (p.1 + p.2 + ℓ + 1) ℓ p t

/-- The empty-stack values `G_p` evaluated with fuel `k`. -/
def Gaux : ℕ → ℕ × ℕ → ℕ
  | 0, _ => 0
  | k + 1, p =>
      (if p = (0, 0) then 1 else 0)
        + (∑ h ∈ Finset.range p.1, Gaux k (h, p.2 + p.1 - 1 - h))
        + ∑ h ∈ Finset.range p.2, ∑ t ∈ S (p.1, h), K (p.2 - 1 - h) (p.1, h) t * Gaux k t

/-- The empty-stack values `G_p` of the two-threshold kernel algorithm. -/
def G (p : ℕ × ℕ) : ℕ := Gaux (p.1 + p.2 + 1) p

end TwoThreshold

/-- **`|Av_n(1342)|` by the one-threshold recurrence** (Proposition 2.10 of the paper). -/
theorem count_1342_literal (n : ℕ) :
    OneThreshold.W n [] =
      Nat.card {σ : Equiv.Perm (Fin n) // ¬ PermPatterns.PermContains σ pattern1342} := by
  sorry

/-- **`|Av_n(1342)|` by the scalar kernel algorithm** (Theorem 2.19 of the paper). -/
theorem count_1342_kernel (n : ℕ) :
    OneThreshold.G n =
      Nat.card {σ : Equiv.Perm (Fin n) // ¬ PermPatterns.PermContains σ pattern1342} := by
  sorry

/-- **`|Av_n(12453)|` by the literal two-threshold recurrence** (Theorem 4.3 of the paper
at `d = 2`). -/
theorem count_12453_literal (n : ℕ) :
    TwoThreshold.H (n, 0) [] =
      Nat.card {σ : Equiv.Perm (Fin n) // ¬ PermPatterns.PermContains σ pattern12453} := by
  sorry

/-- **`|Av_n(12453)|` by the two-threshold kernel algorithm** (Theorem 1.1 and
eq:answer-G of the paper at `d = 2`). -/
theorem count_12453_kernel (n : ℕ) :
    TwoThreshold.G (n, 0) =
      Nat.card {σ : Equiv.Perm (Fin n) // ¬ PermPatterns.PermContains σ pattern12453} := by
  sorry

end Av12453
