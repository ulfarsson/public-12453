/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Av12453.OneThreshold.Defs

/-!
# The scalar transfer kernels for `Av(1342)`

This file defines the objects of the subsection *The scalar kernel algorithm* of Section 2
of the paper *Protected tails and polynomial-time enumeration of permutations avoiding a direct
sum of an increasing pattern and 231*, for `d = 1`,
where `β₁ = ι₁ ⊕ 231 = 1342` (`0`-based `[0, 2, 3, 1]`, `Av12453.beta_one`).  Values and
positions are `0`-based throughout, as in `Av12453.Basic`.

## The kernel

`K ℓ p t` is the paper's `K_ℓ(p, t)`: the total weight of the paths of the recurrence `W`
that start at `W_p((ℓ) ∣ L)` and are stopped at the first exposure of the protected tail
`L`, at `W_t(∅ ∣ L)`.  The value does not depend on `L`, and the paper's
\eqref{eq:scalar-factorization} reads `W_p((ℓ)L) = ∑_{t ≥ 0} K_ℓ(p, t) W_t(L)`; that
factorization is *not* proved here (see `Av12453/OneThreshold/KernelFactor.lean`).  What is
proved here is only that `K`, `D` and `G` satisfy the paper's defining equations
\eqref{eq:scalar-K}, \eqref{eq:scalar-D} and \eqref{eq:scalar-G}, in the form

* `K_zero`  : `K 0 p t = 1_{p = t}` (the identity kernel `K_0`);
* `K_succ_eq` (`1 ≤ ℓ`) : `K ℓ p t` is the sum of the base-move terms
  `∑_{h < p} K_{ℓ+p-1-h}(h, t)`, the endpoint term `D ℓ p t`, and the split terms
  `∑_{a+b = ℓ-1, a,b ≥ 1} ∑_{u ≤ p} K_a(p, u) K_b(u, t)`;
* `D_one`, `D_succ` : `D 1 p t = 1_{p = t}` and `D ℓ p t = 2 K_{ℓ-1}(p, t)` for `ℓ ≥ 2`;
* `G_eq` : `G p = 1_{p = 0} + ∑_{h < p} ∑_{t ≤ h} K_{p-1-h}(h, t) G_t`.

Two deviations from the paper's display, both harmless and both recorded here:

1. The paper sums the split term over *all* `u ≥ 0`; we sum over `u ∈ range (p + 1)`.  The
   two agree because `K a p u = 0` for `u > p` (`KernelSupport.K_eq_zero_of_lt`, the upper
   half of \cref{lem:scalar-support}); the restricted range is what makes the recursion
   terminate on the grade `p + ℓ` without a support lemma in hand.
2. Likewise `G_eq` sums `t` over `range (h + 1)` rather than over all `t ≥ 0`.

## Termination

Both `K` and `G` are defined by fuel-driven auxiliaries, exactly as `Defs.lean` defines `W`,
so that `decide` can evaluate them in the kernel.  `K ℓ p t` evaluates `Kaux` with fuel
`p + ℓ + 1`, one more than the paper's *grade* `p + ℓ`, which is a topological order for the
kernel dependencies (proof of \cref{thm:scalar-algorithm}): a base term has grade
`h + (ℓ + p - 1 - h) = p + ℓ - 1`, the endpoint term has grade `p + ℓ - 1`, and a split
factor has grade `p + a < p + ℓ` or `u + b ≤ p + b < p + ℓ`.  `Kaux_congr` shows that any
fuel exceeding the grade gives the same value.  `G p` evaluates `Gaux` with fuel `p + 1`,
and every `G t` it uses has `t ≤ h < p`.

## Main definitions

* `K` : the scalar kernel table `K_ℓ(p, t)`, \eqref{eq:scalar-K}.
* `D` : the endpoint term `D_ℓ(p, t)`, \eqref{eq:scalar-D}.
* `G` : the empty-stack values `G_p`, \eqref{eq:scalar-G}.

## Main results

* `K_zero`, `K_succ_eq`, `D_eq`, `D_one`, `D_succ`, `G_eq` : the defining equations.
* The `decide` sanity checks at the end reproduce \cref{ex:scalar-kernel}: the kernel rows
  `K_3(0, ·) = (5)`, `K_2(1, ·) = (4, 2)`, `K_1(2, ·) = (3, 1, 1)` and `G_4 = 23`.
-/

namespace Av12453
namespace OneThreshold

/-! ### The kernel table `K` and the endpoint term `D`

`Kaux k ℓ p t` is the fuel-driven evaluation of \eqref{eq:scalar-K}--\eqref{eq:scalar-D}:
it returns `0` once the fuel `k` runs out, and otherwise recurses with one unit less.  The
endpoint term is inlined here (`if ℓ = 0 then 1_{p=t} else 2 * Kaux k ℓ p t` at the head
`ℓ + 1`) and is named `D` after `K` is available. -/

/-- Fuel-driven evaluation of the scalar kernel recurrence \eqref{eq:scalar-K}. -/
private def Kaux : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | _ + 1, 0, p, t => if p = t then 1 else 0
  | k + 1, ℓ + 1, p, t =>
      (∑ h ∈ Finset.range p, Kaux k (ℓ + 1 + p - 1 - h) h t)
        + (if ℓ = 0 then (if p = t then 1 else 0) else 2 * Kaux k ℓ p t)
        + ∑ a ∈ Finset.Ico 1 ℓ, ∑ u ∈ Finset.range (p + 1), Kaux k a p u * Kaux k (ℓ - a) u t

private theorem Kaux_ell_zero (k p t : ℕ) :
    Kaux (k + 1) 0 p t = if p = t then 1 else 0 := rfl

private theorem Kaux_ell_succ (k ℓ p t : ℕ) :
    Kaux (k + 1) (ℓ + 1) p t =
      (∑ h ∈ Finset.range p, Kaux k (ℓ + 1 + p - 1 - h) h t)
        + (if ℓ = 0 then (if p = t then 1 else 0) else 2 * Kaux k ℓ p t)
        + ∑ a ∈ Finset.Ico 1 ℓ,
            ∑ u ∈ Finset.range (p + 1), Kaux k a p u * Kaux k (ℓ - a) u t := rfl

/-- Any two amounts of fuel exceeding the grade `p + ℓ` give the same value. -/
private theorem Kaux_congr : ∀ k k' ℓ p t,
    p + ℓ < k → p + ℓ < k' → Kaux k ℓ p t = Kaux k' ℓ p t := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro k' ℓ p t h1 h2
    obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
    obtain ⟨k1, rfl⟩ : ∃ k1, k' = k1 + 1 := ⟨k' - 1, by omega⟩
    match ℓ with
    | 0 => rw [Kaux_ell_zero, Kaux_ell_zero]
    | j + 1 =>
      rw [Kaux_ell_succ, Kaux_ell_succ]
      have e1 : ∀ h ∈ Finset.range p,
          Kaux k0 (j + 1 + p - 1 - h) h t = Kaux k1 (j + 1 + p - 1 - h) h t := by
        intro h hh
        rw [Finset.mem_range] at hh
        exact ih k0 (by omega) k1 _ h t (by omega) (by omega)
      have e2 : ∀ a ∈ Finset.Ico 1 j,
          (∑ u ∈ Finset.range (p + 1), Kaux k0 a p u * Kaux k0 (j - a) u t) =
            ∑ u ∈ Finset.range (p + 1), Kaux k1 a p u * Kaux k1 (j - a) u t := by
        intro a ha
        rw [Finset.mem_Ico] at ha
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [Finset.mem_range] at hu
        rw [ih k0 (by omega) k1 a p u (by omega) (by omega),
          ih k0 (by omega) k1 (j - a) u t (by omega) (by omega)]
      have e3 : Kaux k0 j p t = Kaux k1 j p t :=
        ih k0 (by omega) k1 j p t (by omega) (by omega)
      rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, e3]

/--
`K ℓ p t` is the paper's `K_ℓ(p, t)` of \eqref{eq:scalar-K}: the total weight of the paths
of `W` that leave the state with control `p` and active head of size `ℓ`, stopped at the
first exposure of the protected tail, at control `t`.  `K 0` is the identity kernel `K_0`.
-/
def K (ℓ p t : ℕ) : ℕ := Kaux (p + ℓ + 1) ℓ p t

private theorem K_eq_Kaux {ℓ p t k : ℕ} (hk : p + ℓ < k) : K ℓ p t = Kaux k ℓ p t :=
  Kaux_congr _ _ _ _ _ (by omega) hk

/-- **The identity kernel**: `K_0(p, t) = 1_{p = t}`. -/
theorem K_zero (p t : ℕ) : K 0 p t = if p = t then 1 else 0 := rfl

/-- The paper's `D_ℓ(p, t)` of \eqref{eq:scalar-D}: the endpoint term of the kernel
recurrence.  It is only used for `ℓ ≥ 1`. -/
def D (ℓ p t : ℕ) : ℕ := if ℓ = 1 then (if p = t then 1 else 0) else 2 * K (ℓ - 1) p t

/-- The definition of `D`, unfolded. -/
theorem D_eq (ℓ p t : ℕ) :
    D ℓ p t = if ℓ = 1 then (if p = t then 1 else 0) else 2 * K (ℓ - 1) p t := rfl

/-- **\eqref{eq:scalar-D}**, first half: `D_1(p, t) = 1_{p = t}`. -/
theorem D_one (p t : ℕ) : D 1 p t = if p = t then 1 else 0 := by
  rw [D_eq, if_pos rfl]

/-- **\eqref{eq:scalar-D}**, second half: `D_ℓ(p, t) = 2 K_{ℓ-1}(p, t)` for `ℓ ≥ 2`. -/
theorem D_succ {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (p t : ℕ) : D ℓ p t = 2 * K (ℓ - 1) p t := by
  rw [D_eq, if_neg (by omega)]

/-- **\eqref{eq:scalar-K}**: the scalar kernel recurrence, for `ℓ ≥ 1`.  The three summands
are the base moves, the endpoint term, and the splits `a + b = ℓ - 1` with `a, b ≥ 1`.  The
paper sums the split over all `u ≥ 0`; here `u` runs over `{0, …, p}`, which by
\cref{lem:scalar-support} carries the whole support of `K_a(p, ·)`. -/
theorem K_succ_eq {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (p t : ℕ) :
    K ℓ p t =
      (∑ h ∈ Finset.range p, K (ℓ + p - 1 - h) h t)
        + D ℓ p t
        + ∑ a ∈ Finset.Ico 1 (ℓ - 1),
            ∑ u ∈ Finset.range (p + 1), K a p u * K (ℓ - 1 - a) u t := by
  obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
  rw [K, show p + (j + 1) + 1 = (p + j + 1) + 1 by omega, Kaux_ell_succ, Nat.add_sub_cancel]
  have e1 : ∀ h ∈ Finset.range p,
      Kaux (p + j + 1) (j + 1 + p - 1 - h) h t = K (j + 1 + p - 1 - h) h t := by
    intro h hh
    rw [Finset.mem_range] at hh
    exact (K_eq_Kaux (by omega)).symm
  have e2 : ∀ a ∈ Finset.Ico 1 j,
      (∑ u ∈ Finset.range (p + 1),
          Kaux (p + j + 1) a p u * Kaux (p + j + 1) (j - a) u t) =
        ∑ u ∈ Finset.range (p + 1), K a p u * K (j - a) u t := by
    intro a ha
    rw [Finset.mem_Ico] at ha
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.mem_range] at hu
    rw [← K_eq_Kaux (k := p + j + 1) (by omega), ← K_eq_Kaux (k := p + j + 1) (by omega)]
  have e3 : (if j = 0 then (if p = t then 1 else 0)
      else 2 * Kaux (p + j + 1) j p t) = D (j + 1) p t := by
    rw [D_eq, Nat.add_sub_cancel]
    by_cases hj : j = 0
    · rw [if_pos hj, if_pos (show j + 1 = 1 by omega)]
    · rw [if_neg hj, if_neg (show ¬ (j + 1 = 1) by omega)]
      exact congrArg _ (K_eq_Kaux (by omega)).symm
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, e3]

/-! ### The empty-stack values `G` -/

/-- Fuel-driven evaluation of \eqref{eq:scalar-G}. -/
private def Gaux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, p =>
      (if p = 0 then 1 else 0)
        + ∑ h ∈ Finset.range p, ∑ t ∈ Finset.range (h + 1), K (p - 1 - h) h t * Gaux k t

private theorem Gaux_succ (k p : ℕ) :
    Gaux (k + 1) p =
      (if p = 0 then 1 else 0)
        + ∑ h ∈ Finset.range p,
            ∑ t ∈ Finset.range (h + 1), K (p - 1 - h) h t * Gaux k t := rfl

/-- Any two amounts of fuel exceeding `p` give the same value. -/
private theorem Gaux_congr : ∀ k k' p, p < k → p < k' → Gaux k p = Gaux k' p := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro k' p h1 h2
    obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
    obtain ⟨k1, rfl⟩ : ∃ k1, k' = k1 + 1 := ⟨k' - 1, by omega⟩
    rw [Gaux_succ, Gaux_succ]
    refine congrArg _ (Finset.sum_congr rfl fun h hh => ?_)
    rw [Finset.mem_range] at hh
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at ht
    rw [ih k0 (by omega) k1 t (by omega) (by omega)]

/--
`G p` is the paper's `G_p = W_p(∅)` of \eqref{eq:scalar-G}, computed from the kernel table
`K` alone.  `G n` is the number of `1342`-avoiding permutations of `{0, …, n-1}`
(`KernelCount.av1342_count_kernel`).
-/
def G (p : ℕ) : ℕ := Gaux (p + 1) p

private theorem G_eq_Gaux {p k : ℕ} (hk : p < k) : G p = Gaux k p :=
  Gaux_congr _ _ _ (by omega) hk

/-- **\eqref{eq:scalar-G}**: the empty-stack values in terms of the kernel table.  The paper
sums `t` over all `t ≥ 0`; here `t` runs over `{0, …, h}`, which by
\cref{lem:scalar-support} carries the whole support of `K_{p-1-h}(h, ·)`. -/
theorem G_eq (p : ℕ) :
    G p = (if p = 0 then 1 else 0)
      + ∑ h ∈ Finset.range p, ∑ t ∈ Finset.range (h + 1), K (p - 1 - h) h t * G t := by
  rw [G, Gaux_succ]
  refine congrArg _ (Finset.sum_congr rfl fun h hh => ?_)
  rw [Finset.mem_range] at hh
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  exact congrArg _ (G_eq_Gaux (by omega)).symm

/-! ### Sanity checks

\cref{ex:scalar-kernel} of the paper, *From kernel rows to `|Av₄(1342)|`*.  Every check
below is a kernel evaluation (`decide`), so it adds no axiom. -/

set_option maxRecDepth 10000 in
/-- The kernel row `K_3(0, ·) = (5)` of \cref{ex:scalar-kernel}. -/
example : K 3 0 0 = 5 := by decide

set_option maxRecDepth 10000 in
/-- The kernel row `K_2(1, ·) = (4, 2)` of \cref{ex:scalar-kernel}. -/
example : K 2 1 0 = 4 := by decide

set_option maxRecDepth 10000 in
/-- The kernel row `K_2(1, ·) = (4, 2)` of \cref{ex:scalar-kernel}. -/
example : K 2 1 1 = 2 := by decide

set_option maxRecDepth 10000 in
/-- The kernel row `K_1(2, ·) = (3, 1, 1)` of \cref{ex:scalar-kernel}. -/
example : K 1 2 0 = 3 := by decide

set_option maxRecDepth 10000 in
/-- The kernel row `K_1(2, ·) = (3, 1, 1)` of \cref{ex:scalar-kernel}. -/
example : K 1 2 1 = 1 := by decide

set_option maxRecDepth 10000 in
/-- The kernel row `K_1(2, ·) = (3, 1, 1)` of \cref{ex:scalar-kernel}. -/
example : K 1 2 2 = 1 := by decide

set_option maxRecDepth 10000 in
/-- The rows above vanish outside `{0, …, p}` (the upper half of \cref{lem:scalar-support},
`KernelSupport.K_eq_zero_of_lt`). -/
example : (K 3 0 1, K 2 1 2, K 1 2 3) = (0, 0, 0) := by decide

set_option maxRecDepth 10000 in
/-- `G_4 = 5G_0 + (4G_0 + 2G_1) + (3G_0 + G_1 + G_2) + G_3 = 23`
(\cref{ex:scalar-kernel}), i.e. `|Av₄(1342)| = 23`. -/
example : G 4 = 23 := by decide

set_option maxRecDepth 100000 in
/-- The first nine terms of `G` (Bona's sequence `|Av_n(1342)|`; the paper's
\eqref{eq:first-terms} is the `d = 2` sequence of `Av(12453)`, not this one).  These are the
same numbers that `Defs.W` produces (`Counting.av1342_count`), as `KernelCount.G_eq_W` will
say. -/
example : (List.range 9).map G = [1, 1, 2, 6, 23, 103, 512, 2740, 15485] := by decide

/-! The same nine values, printed rather than checked (the brief's `#eval`): the next line
reports

    [1, 1, 2, 6, 23, 103, 512, 2740, 15485]

which is `|Av_n(1342)|` for `n = 0, …, 8`. -/

#eval (List.range 9).map G

end OneThreshold
end Av12453
