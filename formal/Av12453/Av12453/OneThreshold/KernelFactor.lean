/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Av12453.OneThreshold.Kernel
import Av12453.OneThreshold.KernelSupport
import Av12453.OneThreshold.Counting

/-!
# The protected-tail factorization of the literal recurrence for `Av(1342)`

This file proves \eqref{eq:scalar-factorization} of the subsection *The scalar kernel
algorithm* of Section 2 of the paper *Protected tails and polynomial-time enumeration of
permutations avoiding a direct sum of an increasing pattern and 231*, for `d = 1`: the
literal recurrence `W` of `Av12453.OneThreshold.Defs` factors
through the scalar transfer kernel `K` of `Av12453.OneThreshold.Kernel`,

    W p ((ℓ) L) = ∑ t, K ℓ p t * W t L      (ℓ ≥ 1),

with `t` running over the support `{0, …, p}` of the kernel row `K_ℓ(p, ·)`
(\cref{lem:scalar-support}).

The abstract protected-tail principle (`thm:protected-tail-principle`) is *not* formalized:
as the report for component 3a recommends, the factorization is proved directly from the
defining equations of `W` and `K`, by the first-move partition that proves
\cref{prop:scalar-kernel-recurrence}.

## The proof

Both `W_eq_cons` and `K_succ_eq` split the same first move into three groups, and the
induction matches them group by group.  The induction is on the *grade* `p + ℓ`, the
paper's topological order for the kernel dependencies, and it is generalized over the
protected tail `L` (the split term needs the statement for the longer tail `(b) L`):

* **base moves.**  For `h < p` the term `W h ((ℓ + p - 1 - h) L)` has grade
  `h + (ℓ + p - 1 - h) = p + ℓ - 1`, so the induction hypothesis rewrites it as
  `∑_{t ≤ h} K_{ℓ+p-1-h}(h, t) W_t(L)`; `K_eq_zero_of_lt` extends the range to `{0, …, p}`.
* **endpoints.**  `E_ℓ(p, L)` is `W_p(L)` for `ℓ = 1`, which is the `D_1(p, t) = 1_{p=t}`
  term, and `2 W_p((ℓ-1) L)` for `ℓ ≥ 2`, which is the induction hypothesis at grade
  `p + ℓ - 1` against `D_ℓ(p, t) = 2 K_{ℓ-1}(p, t)`.
* **splits.**  For `a + b = ℓ - 1` with `a, b ≥ 1`, two applications of the induction
  hypothesis give
  `W_p((a)(b)L) = ∑_{u ≤ p} K_a(p, u) W_u((b) L) = ∑_u K_a(p,u) ∑_t K_b(u,t) W_t(L)`
  (grades `p + a < p + ℓ` and `u + b ≤ p + b < p + ℓ`); `Finset.sum_comm` and the range
  alignment `∑_{t ≤ u} = ∑_{t ≤ p}` turn this into the split term of `K_succ_eq`.

## Main results

* `W_factor_of` : the factorization from an explicit support hypothesis
  `∀ ℓ p t, p < t → K ℓ p t = 0` (the upper half of \cref{lem:scalar-support}).
* `W_factor` : **\eqref{eq:scalar-factorization}**, with the support hypothesis discharged.
* `W_factor_range` : the same with the paper's unrestricted summation range (added at
  integration).
* `W_factor_zero` : the `ℓ = 0` reading `W_p(L) = ∑_{t ≤ p} K_0(p, t) W_t(L)`, i.e. that
  `K_0` is the identity kernel.

## Integration (phase 3)

The support hypothesis of `W_factor_of` is discharged by `KernelSupport.K_eq_zero_of_lt`
(theorem 1 of the component-4a brief (development notes, in git history), the upper half of
\cref{lem:scalar-support}).
While `KernelSupport.lean` was being written in a parallel workspace, this file carried a
`private` copy of that induction; at integration the copy was deleted and the last line of
`W_factor` became `W_factor_of (fun _ _ _ h => K_eq_zero_of_lt h) hℓ p L`.  Nothing else
changed: `W_factor_aux`, `W_factor_of`, `sum_range_extend` and every proof body are as
delivered.
-/

namespace Av12453
namespace OneThreshold

/-! ### Range alignment

The kernel row `K_b(u, ·)` is supported in `{0, …, u}`, so for `u ≤ p` a sum of its entries
against `W_·(L)` may be taken over `{0, …, p}` instead. -/

private theorem sum_range_extend (hK0 : ∀ ℓ p t, p < t → K ℓ p t = 0) {u p : ℕ} (hup : u ≤ p)
    (b : ℕ) (L : List ℕ) :
    (∑ t ∈ Finset.range (p + 1), K b u t * W t L) =
      ∑ t ∈ Finset.range (u + 1), K b u t * W t L := by
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  · intro x hx hnx
    rw [Finset.mem_range] at hx hnx
    rw [hK0 b u x (by omega), Nat.zero_mul]

/-! ### The factorization -/

private theorem W_factor_aux (hK0 : ∀ ℓ p t, p < t → K ℓ p t = 0) :
    ∀ N p ℓ (L : List ℕ), p + ℓ ≤ N → 1 ≤ ℓ →
      W p (ℓ :: L) = ∑ t ∈ Finset.range (p + 1), K ℓ p t * W t L := by
  intro N
  induction N with
  | zero => intro p ℓ L hN hℓ; omega
  | succ N ih =>
    intro p ℓ L hN hℓ
    obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
    -- the base-move group
    have h1 : (∑ t ∈ Finset.range (p + 1),
          (∑ h ∈ Finset.range p, K (j + 1 + p - 1 - h) h t) * W t L)
        = ∑ h ∈ Finset.range p, W h ((j + 1 + p - 1 - h) :: L) := by
      calc (∑ t ∈ Finset.range (p + 1),
              (∑ h ∈ Finset.range p, K (j + 1 + p - 1 - h) h t) * W t L)
          = ∑ t ∈ Finset.range (p + 1),
              ∑ h ∈ Finset.range p, K (j + 1 + p - 1 - h) h t * W t L :=
            Finset.sum_congr rfl fun t _ => by rw [Finset.sum_mul]
        _ = ∑ h ∈ Finset.range p,
              ∑ t ∈ Finset.range (p + 1), K (j + 1 + p - 1 - h) h t * W t L :=
            Finset.sum_comm
        _ = ∑ h ∈ Finset.range p, W h ((j + 1 + p - 1 - h) :: L) := by
            refine Finset.sum_congr rfl fun h hh => ?_
            rw [Finset.mem_range] at hh
            rw [sum_range_extend hK0 (show h ≤ p by omega) _ L]
            exact (ih h (j + 1 + p - 1 - h) L (by omega) (by omega)).symm
    -- the endpoint group
    have h2 : (∑ t ∈ Finset.range (p + 1), D (j + 1) p t * W t L) = Eend (j + 1) p L := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [Nat.zero_add, W_endpoint_one]
        simp [D_one, Finset.sum_ite_eq]
      · rw [W_endpoint_two_le (show 2 ≤ j + 1 by omega), Nat.add_sub_cancel,
          ih p j L (by omega) hj, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [D_succ (show 2 ≤ j + 1 by omega), Nat.add_sub_cancel, mul_assoc]
    -- the split group
    have h3 : (∑ t ∈ Finset.range (p + 1),
          (∑ a ∈ Finset.Ico 1 j, ∑ u ∈ Finset.range (p + 1), K a p u * K (j - a) u t)
            * W t L)
        = ∑ a ∈ Finset.Ico 1 j, W p (a :: (j - a) :: L) := by
      calc (∑ t ∈ Finset.range (p + 1),
              (∑ a ∈ Finset.Ico 1 j, ∑ u ∈ Finset.range (p + 1), K a p u * K (j - a) u t)
                * W t L)
          = ∑ t ∈ Finset.range (p + 1), ∑ a ∈ Finset.Ico 1 j,
              (∑ u ∈ Finset.range (p + 1), K a p u * K (j - a) u t) * W t L :=
            Finset.sum_congr rfl fun t _ => by rw [Finset.sum_mul]
        _ = ∑ a ∈ Finset.Ico 1 j, ∑ t ∈ Finset.range (p + 1),
              (∑ u ∈ Finset.range (p + 1), K a p u * K (j - a) u t) * W t L :=
            Finset.sum_comm
        _ = ∑ a ∈ Finset.Ico 1 j, W p (a :: (j - a) :: L) := by
            refine Finset.sum_congr rfl fun a ha => ?_
            rw [Finset.mem_Ico] at ha
            calc (∑ t ∈ Finset.range (p + 1),
                    (∑ u ∈ Finset.range (p + 1), K a p u * K (j - a) u t) * W t L)
                = ∑ t ∈ Finset.range (p + 1), ∑ u ∈ Finset.range (p + 1),
                    K a p u * (K (j - a) u t * W t L) := by
                  refine Finset.sum_congr rfl fun t _ => ?_
                  rw [Finset.sum_mul]
                  exact Finset.sum_congr rfl fun u _ => by rw [mul_assoc]
              _ = ∑ u ∈ Finset.range (p + 1), ∑ t ∈ Finset.range (p + 1),
                    K a p u * (K (j - a) u t * W t L) := Finset.sum_comm
              _ = ∑ u ∈ Finset.range (p + 1), K a p u * W u ((j - a) :: L) := by
                  refine Finset.sum_congr rfl fun u hu => ?_
                  rw [Finset.mem_range] at hu
                  rw [← Finset.mul_sum, sum_range_extend hK0 (show u ≤ p by omega) (j - a) L,
                    ← ih u (j - a) L (by omega) (by omega)]
              _ = W p (a :: (j - a) :: L) :=
                  (ih p a ((j - a) :: L) (by omega) (by omega)).symm
    rw [W_eq_cons hℓ p L]
    simp only [Nat.add_sub_cancel]
    rw [← h1, ← h2, ← h3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [K_succ_eq hℓ p t]
    simp only [Nat.add_sub_cancel]
    ring

/-- **\eqref{eq:scalar-factorization}**, relative to the upper half of
\cref{lem:scalar-support}: with `hK0` the statement that a kernel row `K_ℓ(p, ·)` vanishes
above `p`, the literal recurrence factors through the scalar kernel.  This is the
hypothesis-parametric form, so that it is independent of `KernelSupport.lean`. -/
theorem W_factor_of (hK0 : ∀ ℓ p t, p < t → K ℓ p t = 0) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (p : ℕ)
    (L : List ℕ) : W p (ℓ :: L) = ∑ t ∈ Finset.range (p + 1), K ℓ p t * W t L :=
  W_factor_aux hK0 (p + ℓ) p ℓ L le_rfl hℓ

/-- **\eqref{eq:scalar-factorization}**: the protected-tail factorization of the literal
recurrence `W` through the scalar kernel `K`.  The paper sums over all `t ≥ 0`; the range
`{0, …, p}` carries the whole support of `K_ℓ(p, ·)` by \cref{lem:scalar-support}. -/
theorem W_factor {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (p : ℕ) (L : List ℕ) :
    W p (ℓ :: L) = ∑ t ∈ Finset.range (p + 1), K ℓ p t * W t L :=
  W_factor_of (fun _ _ _ h => K_eq_zero_of_lt h) hℓ p L

/-- **\eqref{eq:scalar-factorization} with the paper's summation range**: the factorization
may be summed over any `Finset.range N` with `N ≥ p + 1`, because the row `K_ℓ(p, ·)`
vanishes above `p` (`KernelSupport.K_eq_zero_of_lt`).  This is the paper's `∑_{t ≥ 0}`,
read finitarily.  (Added at integration, phase 3.) -/
theorem W_factor_range {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (p : ℕ) (L : List ℕ) {N : ℕ} (hN : p + 1 ≤ N) :
    W p (ℓ :: L) = ∑ t ∈ Finset.range N, K ℓ p t * W t L := by
  rw [W_factor hℓ p L, K_sum_extend hN ℓ (fun t => W t L)]

/-- The `ℓ = 0` reading of \eqref{eq:scalar-factorization}: `K_0` is the identity kernel, so
the factorization at `ℓ = 0` is the tautology `W_p(L) = W_p(L)`.  Together with `W_factor`
this covers every `ℓ ≥ 0`. -/
theorem W_factor_zero (p : ℕ) (L : List ℕ) :
    W p L = ∑ t ∈ Finset.range (p + 1), K 0 p t * W t L := by
  simp [K_zero, Finset.sum_ite_eq]

/-! ### Interface and sanity checks

The first `example` fixes the statement of `W_factor` at compile time: it is exactly the
frozen statement of theorem 4 of the component-4a brief (development notes, in git history), so
any later drift in the
binders or in the summation range is caught here.  The `decide` checks below evaluate both
sides of \eqref{eq:scalar-factorization} in the kernel, on tails of length `0`, `1` and `2`;
they add no axiom. -/

/-- Statement check: `W_factor` has exactly the frozen type of theorem 4 of the brief. -/
example : ∀ {ℓ : ℕ}, 1 ≤ ℓ → ∀ (p : ℕ) (L : List ℕ),
    W p (ℓ :: L) = ∑ t ∈ Finset.range (p + 1), K ℓ p t * W t L := @W_factor

/-- Statement check for the `ℓ = 0` reading. -/
example : ∀ (p : ℕ) (L : List ℕ),
    W p L = ∑ t ∈ Finset.range (p + 1), K 0 p t * W t L := @W_factor_zero

set_option maxRecDepth 100000 in
/-- `W_3((3)) = ∑_{t ≤ 3} K_3(3, t) W_t(∅)`: an empty protected tail. -/
example : W 3 [3] = ∑ t ∈ Finset.range 4, K 3 3 t * W t [] := by decide

set_option maxRecDepth 100000 in
/-- `W_3((2) 1) = ∑_{t ≤ 3} K_2(3, t) W_t((1))`: a protected tail of one block. -/
example : W 3 [2, 1] = ∑ t ∈ Finset.range 4, K 2 3 t * W t [1] := by decide

set_option maxRecDepth 100000 in
/-- `W_2((1) 2 1) = ∑_{t ≤ 2} K_1(2, t) W_t((2)(1))`: a protected tail of two blocks. -/
example : W 2 [1, 2, 1] = ∑ t ∈ Finset.range 3, K 1 2 t * W t [2, 1] := by decide

set_option maxRecDepth 100000 in
/-- The `ℓ = 0` reading at `p = 4`, `L = (2)(1)`. -/
example : W 4 [2, 1] = ∑ t ∈ Finset.range 5, K 0 4 t * W t [2, 1] := by decide

end OneThreshold
end Av12453
