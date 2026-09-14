/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Av12453.TwoThreshold.Defs
import Av12453.OneThreshold.Kernel

/-!
# The transfer kernels for `Av(12453)` (`d = 2`)

This file defines the objects of the section *Protected tails and transfer kernels*
(`sec:kernels`) of the paper *Protected tails and polynomial-time enumeration of permutations
avoiding a direct sum of an increasing pattern and 231*,
specialized to `d = 2`, where `β₂ = ι₂ ⊕ 231 = 12453` (`0`-based `[0, 1, 3, 4, 2]`,
`Av12453.beta_two`).  Values, positions and controls are `0`-based throughout, as in
`Av12453.Basic`; the control is a pair `𝐩 = (p₀, p₁) : ℕ × ℕ` and its *mass* is
`‖𝐩‖₁ = p₀ + p₁`.

## The kernel

`K ℓ 𝐩 𝐭` is the paper's `K_ℓ(𝐩, 𝐭)`: the total weight of the paths of the recurrence `H`
that start at `H_𝐩((ℓ) ∣ L)` and are stopped at the first exposure of the protected tail
`L`, at `H_𝐭(∅ ∣ L)`.  By \cref{cor:protected-tail} the value does not depend on `L`, and
\eqref{eq:factorization} reads `H_𝐩((ℓ)L) = ∑_𝐭 K_ℓ(𝐩, 𝐭) H_𝐭(L)`; that factorization is
*not* proved here (see `Av12453/TwoThreshold/KernelFactor.lean`).  What is proved here is
only that `K`, `D` and `G` satisfy the paper's defining equations \eqref{eq:K},
\eqref{eq:D} and \eqref{eq:G}, in the form

* `K_zero`  : `K 0 𝐩 𝐭 = 1_{𝐩 = 𝐭}` (the boundary kernel `K_0`);
* `K_succ_eq` (`1 ≤ ℓ`) : `K ℓ 𝐩 𝐭` is the sum of the early-band terms
  `∑_{h < p₀} K_ℓ(T_{0,h}(𝐩), 𝐭)`, the last-band terms
  `∑_{h < p₁} K_{ℓ+δ_h}(U_h(𝐩), 𝐭)`, the endpoint term `D ℓ 𝐩 𝐭`, and the split terms
  `∑_{a+b = ℓ-1, a,b ≥ 1} ∑_{‖𝐮‖₁ ≤ ‖𝐩‖₁} K_a(𝐩, 𝐮) K_b(𝐮, 𝐭)`;
* `D_one`, `D_succ` : `D 1 𝐩 𝐭 = 1_{𝐩 = 𝐭}` and `D ℓ 𝐩 𝐭 = 2 K_{ℓ-1}(𝐩, 𝐭)` for `ℓ ≥ 2`;
* `G_eq` : \eqref{eq:G}.

Here, by \eqref{eq:T} and \eqref{eq:U} at `d = 2`,

    T_{0,h}(p₀, p₁) = (h, p₁ + p₀ - 1 - h),     U_h(p₀, p₁) = (p₀, h),
    δ_h = p₁ - 1 - h,

exactly as in the four lines of \eqref{eq:H} formalized by `TwoThreshold.Defs.H_eq_cons`.

Two deviations from the paper's display, both harmless and both recorded here:

1. The paper sums the split term over *all* controls `𝐮`; we sum over
   `𝐮 ∈ S 𝐩 = ctrls ‖𝐩‖₁`, the finitely many controls of mass at most `‖𝐩‖₁`.  The two
   agree because `K a 𝐩 𝐮 = 0` once `‖𝐩‖₁ < ‖𝐮‖₁` (`KernelSupport.K_eq_zero_of_mass_lt`,
   which is the half of \cref{lem:support} that bounds the mass); the restricted index set
   is what makes the recursion terminate on the grade `‖𝐩‖₁ + ℓ` without a support lemma in
   hand.
2. Likewise `G_eq` sums `𝐭` over `S (p₀, h)` rather than over all controls.

## Termination

Both `K` and `G` are defined by fuel-driven auxiliaries, exactly as `Defs.lean` defines `H`,
so that `decide` can evaluate them in the kernel.  `K ℓ 𝐩 𝐭` evaluates `Kaux` with fuel
`‖𝐩‖₁ + ℓ + 1`, one more than the paper's *grade* `w = ‖𝐩‖₁ + ℓ`, which `sec:algorithm`
verifies is a topological order for the kernel dependencies of \eqref{eq:K}:

* an early-band term has grade `(h + (p₁ + p₀ - 1 - h)) + ℓ = w - 1`;
* a last-band term has grade `(p₀ + h) + (ℓ + δ_h) = w - 1` (the paper's displayed
  computation `‖U_h(𝐩)‖₁ + (ℓ + δ_h) = ‖𝐩‖₁ - (δ_h + 1) + ℓ + δ_h = w - 1`);
* the endpoint term `D_ℓ` for `ℓ ≥ 2` uses grade `w - 1`, and `D_1` is initial data;
* a split factor has grade `‖𝐩‖₁ + a < w` or `‖𝐮‖₁ + b ≤ ‖𝐩‖₁ + b < w`, the latter because
  the index set `S 𝐩` truncates `𝐮` to mass at most `‖𝐩‖₁`.

`Kaux_congr` shows that any fuel exceeding the grade gives the same value.  `G 𝐩` evaluates
`Gaux` with fuel `‖𝐩‖₁ + 1`, and every `G 𝐭` it uses has `‖𝐭‖₁ ≤ p₀ + h < ‖𝐩‖₁`; this is
the paper's "in the empty-stack phase every terminal control used at mass `m` has smaller
mass, including `U_h(𝐩)` when `K_0` occurs".

## Main definitions

* `ctrls M` : the finite set of controls of mass at most `M`; `S 𝐩 = ctrls ‖𝐩‖₁`.
* `K` : the transfer-kernel table `K_ℓ(𝐩, 𝐭)`, \eqref{eq:K}.
* `D` : the endpoint term `D_ℓ(𝐩, 𝐭)`, \eqref{eq:D}.
* `G` : the empty-stack values `G_𝐩`, \eqref{eq:G}.

## Main results

* `mem_ctrls`, `ctrls_mono`, `mem_S`, `S_mono` : the index-set API.
* `K_zero`, `K_succ_eq`, `D_eq`, `D_one`, `D_succ`, `G_eq` : the defining equations.
* The `decide` and `#eval` sanity checks at the end: two kernel rows, the cross-link with
  the `d = 1` kernel of `Av12453.OneThreshold`, and
  `G_{(n,0)} = 1, 1, 2, 6, 24, 119, 694, 4581, 33286, 260927` — the paper's
  \eqref{eq:first-terms}, which `TwoThreshold.Counting.av12453_count` proves is
  `|Av_n(12453)|`.
-/

namespace Av12453
namespace TwoThreshold

/-! ### The index set of controls

\cref{lem:support} bounds the terminal controls of a kernel row by the mass of its source
control, so every sum over controls that occurs in \eqref{eq:K} and \eqref{eq:G} may be
taken over the finite set `ctrls M = {𝐮 : ‖𝐮‖₁ ≤ M}`.  Only `mem_ctrls` and `ctrls_mono`
are ever used; the concrete `Finset` below is an implementation detail. -/

/-- The controls of mass at most `M`, as a `Finset (ℕ × ℕ)`. -/
def ctrls (M : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter fun u => u.1 + u.2 ≤ M

/-- **Membership in `ctrls`**: `ctrls M` is exactly the set of controls of mass at most
`M`. -/
@[simp] theorem mem_ctrls {M : ℕ} {u : ℕ × ℕ} : u ∈ ctrls M ↔ u.1 + u.2 ≤ M := by
  rw [ctrls, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  omega

/-- `ctrls` is monotone in the mass bound. -/
theorem ctrls_mono {M M' : ℕ} (h : M ≤ M') : ctrls M ⊆ ctrls M' := by
  intro u hu
  rw [mem_ctrls] at hu ⊢
  omega

/-- The index set attached to a source control `𝐩`: the controls of mass at most `‖𝐩‖₁`.
This is the paper's summation range in \eqref{eq:K} truncated by \cref{lem:support}. -/
def S (p : ℕ × ℕ) : Finset (ℕ × ℕ) := ctrls (p.1 + p.2)

theorem S_def (p : ℕ × ℕ) : S p = ctrls (p.1 + p.2) := rfl

/-- **Membership in `S`**. -/
@[simp] theorem mem_S {p t : ℕ × ℕ} : t ∈ S p ↔ t.1 + t.2 ≤ p.1 + p.2 := mem_ctrls

theorem S_mono {p p' : ℕ × ℕ} (h : p.1 + p.2 ≤ p'.1 + p'.2) : S p ⊆ S p' := ctrls_mono h

theorem S_subset_ctrls {p : ℕ × ℕ} {M : ℕ} (h : p.1 + p.2 ≤ M) : S p ⊆ ctrls M :=
  ctrls_mono h

/-! ### The kernel table `K` and the endpoint term `D`

`Kaux k ℓ 𝐩 𝐭` is the fuel-driven evaluation of \eqref{eq:K}--\eqref{eq:D}: it returns `0`
once the fuel `k` runs out, and otherwise recurses with one unit less.  The endpoint term
is inlined here (`if ℓ = 0 then 1_{𝐩=𝐭} else 2 * Kaux k ℓ 𝐩 𝐭` at the head `ℓ + 1`) and is
named `D` after `K` is available. -/

/-- Fuel-driven evaluation of the two-threshold kernel recurrence \eqref{eq:K}. -/
private def Kaux : ℕ → ℕ → ℕ × ℕ → ℕ × ℕ → ℕ
  | 0, _, _, _ => 0
  | _ + 1, 0, p, t => if p = t then 1 else 0
  | k + 1, ℓ + 1, p, t =>
      (∑ h ∈ Finset.range p.1, Kaux k (ℓ + 1) (h, p.2 + p.1 - 1 - h) t)
        + (∑ h ∈ Finset.range p.2, Kaux k (ℓ + 1 + (p.2 - 1 - h)) (p.1, h) t)
        + (if ℓ = 0 then (if p = t then 1 else 0) else 2 * Kaux k ℓ p t)
        + ∑ a ∈ Finset.Ico 1 ℓ, ∑ u ∈ S p, Kaux k a p u * Kaux k (ℓ - a) u t

private theorem Kaux_ell_zero (k : ℕ) (p t : ℕ × ℕ) :
    Kaux (k + 1) 0 p t = if p = t then 1 else 0 := rfl

private theorem Kaux_ell_succ (k ℓ : ℕ) (p t : ℕ × ℕ) :
    Kaux (k + 1) (ℓ + 1) p t =
      (∑ h ∈ Finset.range p.1, Kaux k (ℓ + 1) (h, p.2 + p.1 - 1 - h) t)
        + (∑ h ∈ Finset.range p.2, Kaux k (ℓ + 1 + (p.2 - 1 - h)) (p.1, h) t)
        + (if ℓ = 0 then (if p = t then 1 else 0) else 2 * Kaux k ℓ p t)
        + ∑ a ∈ Finset.Ico 1 ℓ, ∑ u ∈ S p, Kaux k a p u * Kaux k (ℓ - a) u t := rfl

/-- Any two amounts of fuel exceeding the grade `w = ‖𝐩‖₁ + ℓ` give the same value. -/
private theorem Kaux_congr : ∀ k k' ℓ (p t : ℕ × ℕ),
    p.1 + p.2 + ℓ < k → p.1 + p.2 + ℓ < k' → Kaux k ℓ p t = Kaux k' ℓ p t := by
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
      have e1 : ∀ h ∈ Finset.range p.1,
          Kaux k0 (j + 1) (h, p.2 + p.1 - 1 - h) t
            = Kaux k1 (j + 1) (h, p.2 + p.1 - 1 - h) t := by
        intro h hh
        rw [Finset.mem_range] at hh
        exact ih k0 (by omega) k1 _ _ t (by simp; omega) (by simp; omega)
      have e2 : ∀ h ∈ Finset.range p.2,
          Kaux k0 (j + 1 + (p.2 - 1 - h)) (p.1, h) t
            = Kaux k1 (j + 1 + (p.2 - 1 - h)) (p.1, h) t := by
        intro h hh
        rw [Finset.mem_range] at hh
        exact ih k0 (by omega) k1 _ _ t (by simp; omega) (by simp; omega)
      have e3 : ∀ a ∈ Finset.Ico 1 j,
          (∑ u ∈ S p, Kaux k0 a p u * Kaux k0 (j - a) u t) =
            ∑ u ∈ S p, Kaux k1 a p u * Kaux k1 (j - a) u t := by
        intro a ha
        rw [Finset.mem_Ico] at ha
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [mem_S] at hu
        rw [ih k0 (by omega) k1 a p u (by omega) (by omega),
          ih k0 (by omega) k1 (j - a) u t (by omega) (by omega)]
      have e4 : Kaux k0 j p t = Kaux k1 j p t :=
        ih k0 (by omega) k1 j p t (by omega) (by omega)
      rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3, e4]

/--
`K ℓ 𝐩 𝐭` is the paper's `K_ℓ(𝐩, 𝐭)` of \eqref{eq:K}: the total weight of the paths of `H`
that leave the state with control `𝐩` and active head of size `ℓ`, stopped at the first
exposure of the protected tail, at control `𝐭`.  `K 0` is the boundary kernel `K_0`.
-/
def K (ℓ : ℕ) (p t : ℕ × ℕ) : ℕ := Kaux (p.1 + p.2 + ℓ + 1) ℓ p t

private theorem K_eq_Kaux {ℓ : ℕ} {p t : ℕ × ℕ} {k : ℕ} (hk : p.1 + p.2 + ℓ < k) :
    K ℓ p t = Kaux k ℓ p t :=
  Kaux_congr _ _ _ _ _ (by omega) hk

/-- **The boundary kernel**: `K_0(𝐩, 𝐭) = 1_{𝐩 = 𝐭}`. -/
theorem K_zero (p t : ℕ × ℕ) : K 0 p t = if p = t then 1 else 0 := rfl

/-- The paper's `D_ℓ(𝐩, 𝐭)` of \eqref{eq:D}: the endpoint term of the kernel recurrence.
It is only used for `ℓ ≥ 1`. -/
def D (ℓ : ℕ) (p t : ℕ × ℕ) : ℕ :=
  if ℓ = 1 then (if p = t then 1 else 0) else 2 * K (ℓ - 1) p t

/-- The definition of `D`, unfolded. -/
theorem D_eq (ℓ : ℕ) (p t : ℕ × ℕ) :
    D ℓ p t = if ℓ = 1 then (if p = t then 1 else 0) else 2 * K (ℓ - 1) p t := rfl

/-- **\eqref{eq:D}**, first half: `D_1(𝐩, 𝐭) = 1_{𝐩 = 𝐭}`. -/
theorem D_one (p t : ℕ × ℕ) : D 1 p t = if p = t then 1 else 0 := by
  rw [D_eq, if_pos rfl]

/-- **\eqref{eq:D}**, second half: `D_ℓ(𝐩, 𝐭) = 2 K_{ℓ-1}(𝐩, 𝐭)` for `ℓ ≥ 2`. -/
theorem D_succ {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (p t : ℕ × ℕ) : D ℓ p t = 2 * K (ℓ - 1) p t := by
  rw [D_eq, if_neg (by omega)]

/-- **\eqref{eq:K}** at `d = 2`: the transfer-kernel recurrence, for `ℓ ≥ 1`.  The four
summands are the early-band moves `T_{0,h}`, the last-band moves `U_h` (which enlarge the
active head by `δ_h = p₁ - 1 - h`), the endpoint term `D_ℓ`, and the splits
`a + b = ℓ - 1` with `a, b ≥ 1`.  The paper sums the split over all controls `𝐮`; here `𝐮`
runs over `S 𝐩 = {𝐮 : ‖𝐮‖₁ ≤ ‖𝐩‖₁}`, which by \cref{lem:support} carries the whole support
of `K_a(𝐩, ·)`. -/
theorem K_succ_eq {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (p t : ℕ × ℕ) :
    K ℓ p t =
      (∑ h ∈ Finset.range p.1, K ℓ (h, p.2 + p.1 - 1 - h) t)
        + (∑ h ∈ Finset.range p.2, K (ℓ + (p.2 - 1 - h)) (p.1, h) t)
        + D ℓ p t
        + ∑ a ∈ Finset.Ico 1 (ℓ - 1), ∑ u ∈ S p, K a p u * K (ℓ - 1 - a) u t := by
  obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
  rw [K, show p.1 + p.2 + (j + 1) + 1 = (p.1 + p.2 + j + 1) + 1 by omega, Kaux_ell_succ,
    Nat.add_sub_cancel]
  have e1 : ∀ h ∈ Finset.range p.1,
      Kaux (p.1 + p.2 + j + 1) (j + 1) (h, p.2 + p.1 - 1 - h) t
        = K (j + 1) (h, p.2 + p.1 - 1 - h) t := by
    intro h hh
    rw [Finset.mem_range] at hh
    exact (K_eq_Kaux (by simp; omega)).symm
  have e2 : ∀ h ∈ Finset.range p.2,
      Kaux (p.1 + p.2 + j + 1) (j + 1 + (p.2 - 1 - h)) (p.1, h) t
        = K (j + 1 + (p.2 - 1 - h)) (p.1, h) t := by
    intro h hh
    rw [Finset.mem_range] at hh
    exact (K_eq_Kaux (by simp; omega)).symm
  have e3 : ∀ a ∈ Finset.Ico 1 j,
      (∑ u ∈ S p, Kaux (p.1 + p.2 + j + 1) a p u * Kaux (p.1 + p.2 + j + 1) (j - a) u t) =
        ∑ u ∈ S p, K a p u * K (j - a) u t := by
    intro a ha
    rw [Finset.mem_Ico] at ha
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [mem_S] at hu
    rw [← K_eq_Kaux (k := p.1 + p.2 + j + 1) (by omega),
      ← K_eq_Kaux (k := p.1 + p.2 + j + 1) (by omega)]
  have e4 : (if j = 0 then (if p = t then 1 else 0)
      else 2 * Kaux (p.1 + p.2 + j + 1) j p t) = D (j + 1) p t := by
    rw [D_eq, Nat.add_sub_cancel]
    by_cases hj : j = 0
    · rw [if_pos hj, if_pos (show j + 1 = 1 by omega)]
    · rw [if_neg hj, if_neg (show ¬ (j + 1 = 1) by omega)]
      exact congrArg _ (K_eq_Kaux (by omega)).symm
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3, e4]

/-! ### The empty-stack values `G` -/

/-- Fuel-driven evaluation of \eqref{eq:G} at `d = 2`. -/
private def Gaux : ℕ → ℕ × ℕ → ℕ
  | 0, _ => 0
  | k + 1, p =>
      (if p = (0, 0) then 1 else 0)
        + (∑ h ∈ Finset.range p.1, Gaux k (h, p.2 + p.1 - 1 - h))
        + ∑ h ∈ Finset.range p.2, ∑ t ∈ S (p.1, h), K (p.2 - 1 - h) (p.1, h) t * Gaux k t

private theorem Gaux_succ (k : ℕ) (p : ℕ × ℕ) :
    Gaux (k + 1) p =
      (if p = (0, 0) then 1 else 0)
        + (∑ h ∈ Finset.range p.1, Gaux k (h, p.2 + p.1 - 1 - h))
        + ∑ h ∈ Finset.range p.2,
            ∑ t ∈ S (p.1, h), K (p.2 - 1 - h) (p.1, h) t * Gaux k t := rfl

/-- Any two amounts of fuel exceeding the mass `‖𝐩‖₁` give the same value. -/
private theorem Gaux_congr : ∀ k k' (p : ℕ × ℕ),
    p.1 + p.2 < k → p.1 + p.2 < k' → Gaux k p = Gaux k' p := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro k' p h1 h2
    obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
    obtain ⟨k1, rfl⟩ : ∃ k1, k' = k1 + 1 := ⟨k' - 1, by omega⟩
    rw [Gaux_succ, Gaux_succ]
    have e1 : ∀ h ∈ Finset.range p.1,
        Gaux k0 (h, p.2 + p.1 - 1 - h) = Gaux k1 (h, p.2 + p.1 - 1 - h) := by
      intro h hh
      rw [Finset.mem_range] at hh
      exact ih k0 (by omega) k1 _ (by simp; omega) (by simp; omega)
    have e2 : ∀ h ∈ Finset.range p.2,
        (∑ t ∈ S (p.1, h), K (p.2 - 1 - h) (p.1, h) t * Gaux k0 t) =
          ∑ t ∈ S (p.1, h), K (p.2 - 1 - h) (p.1, h) t * Gaux k1 t := by
      intro h hh
      rw [Finset.mem_range] at hh
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [mem_S] at ht
      simp only at ht
      rw [ih k0 (by omega) k1 t (by omega) (by omega)]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]

/--
`G 𝐩` is the paper's `G_𝐩 = H_𝐩(∅)` of \eqref{eq:G}, computed from the kernel table `K`
alone.  `G (n, 0)` is the number of `12453`-avoiding permutations of `{0, …, n-1}`
(\eqref{eq:answer-G}; `KernelCount.av12453_count_kernel`).
-/
def G (p : ℕ × ℕ) : ℕ := Gaux (p.1 + p.2 + 1) p

private theorem G_eq_Gaux {p : ℕ × ℕ} {k : ℕ} (hk : p.1 + p.2 < k) : G p = Gaux k p :=
  Gaux_congr _ _ _ (by omega) hk

/-- **\eqref{eq:G}** at `d = 2`: the empty-stack values in terms of the kernel table.  The
three summands are the indicator `1_{𝐩 = 𝟎}`, the early-band sum `∑_{h < p₀} G_{T_{0,h}(𝐩)}`
and the last-band sum `∑_{h < p₁} ∑_𝐭 K_{δ_h}(U_h(𝐩), 𝐭) G_𝐭`.  The paper sums `𝐭` over all
controls; here `𝐭` runs over `S (p₀, h)`, which by \cref{lem:support} carries the whole
support of `K_{δ_h}(U_h(𝐩), ·)`. -/
theorem G_eq (p : ℕ × ℕ) :
    G p = (if p = (0, 0) then 1 else 0)
      + (∑ h ∈ Finset.range p.1, G (h, p.2 + p.1 - 1 - h))
      + ∑ h ∈ Finset.range p.2, ∑ t ∈ S (p.1, h), K (p.2 - 1 - h) (p.1, h) t * G t := by
  rw [G, Gaux_succ]
  have e1 : ∀ h ∈ Finset.range p.1,
      Gaux (p.1 + p.2) (h, p.2 + p.1 - 1 - h) = G (h, p.2 + p.1 - 1 - h) := by
    intro h hh
    rw [Finset.mem_range] at hh
    exact (G_eq_Gaux (by simp; omega)).symm
  have e2 : ∀ h ∈ Finset.range p.2,
      (∑ t ∈ S (p.1, h), K (p.2 - 1 - h) (p.1, h) t * Gaux (p.1 + p.2) t) =
        ∑ t ∈ S (p.1, h), K (p.2 - 1 - h) (p.1, h) t * G t := by
    intro h hh
    rw [Finset.mem_range] at hh
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [mem_S] at ht
    simp only at ht
    rw [← G_eq_Gaux (k := p.1 + p.2) (by omega)]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]

/-! ### Sanity checks

Every `decide` below is a kernel evaluation of `K` or `G`, so it adds no axiom; the three
`#eval`s are guarded by `#guard_msgs`, so the build fails if a value ever changes.

The two kernel rows are the running example's controls.  Note the shape of
\eqref{eq:support} in the second one: `K_1((4,0), ·)` is nonzero at its own source control
`(4,0)`, and elsewhere only at controls of mass at most `3` -- in particular it vanishes at
`(0,4)`, which has the *same* mass `4` but is a different control. -/

/-- The controls of `ctrls 3`, listed in increasing lexicographic order.  Used only to
present the kernel row below. -/
private def ctrls3 : List (ℕ × ℕ) :=
  [(0,0), (0,1), (0,2), (0,3), (1,0), (1,1), (1,2), (2,0), (2,1), (3,0)]

/-- The controls of `ctrls 4`, listed in increasing lexicographic order. -/
private def ctrls4 : List (ℕ × ℕ) :=
  [(0,0), (0,1), (0,2), (0,3), (0,4), (1,0), (1,1), (1,2), (1,3), (2,0), (2,1), (2,2),
   (3,0), (3,1), (4,0)]

set_option maxRecDepth 10000 in
/-- `ctrls3` really is `ctrls 3`, and `ctrls4` really is `ctrls 4`. -/
example : ∀ u ∈ ctrls3, u ∈ ctrls 3 := by decide

set_option maxRecDepth 10000 in
example : ∀ u ∈ ctrls4, u ∈ ctrls 4 := by decide

set_option maxRecDepth 10000 in
/-- The kernel row `K_3((1,2), ·)`. -/
example : ctrls3.map (fun t => K 3 (1, 2) t) = [330, 60, 15, 0, 66, 15, 5, 0, 0, 0] := by
  decide

set_option maxRecDepth 10000 in
/-- The kernel row `K_1((4,0), ·)`. -/
example : ctrls4.map (fun t => K 1 (4, 0) t) =
    [35, 11, 4, 1, 0, 7, 3, 1, 0, 2, 1, 0, 1, 0, 1] := by decide

set_option maxRecDepth 10000 in
/-- Both rows vanish outside `{𝐩} ∪ {𝐭 : ‖𝐭‖₁ < ‖𝐩‖₁}` (\cref{lem:support}). -/
example : (K 3 (1, 2) (2, 2), K 3 (1, 2) (0, 4), K 1 (4, 0) (0, 4), K 1 (4, 0) (5, 0))
    = (0, 0, 0, 0) := by decide

set_option maxRecDepth 10000 in
/-- The boundary kernel `K_0 = 1_{𝐩 = 𝐭}`. -/
example : (K 0 (1, 2) (1, 2), K 0 (1, 2) (2, 1)) = (1, 0) := by decide

set_option maxRecDepth 400000 in
/-- `G_{(n,0)} = |Av_n(12453)|` for `n ≤ 6` (the paper's \eqref{eq:first-terms}); that these
are the avoider counts is `KernelCount.av12453_count_kernel`, and that they are the values
of the literal recurrence \eqref{eq:H} is `TwoThreshold.Counting.av12453_count`. -/
example : (List.range 7).map (fun n => G (n, 0)) = [1, 1, 2, 6, 24, 119, 694] := by decide

/-! ### The cross-link with the `d = 1` kernel

The controls `(0, q)` carry no early band, so \eqref{eq:K} at such a control is literally the
`d = 1` recurrence \eqref{eq:scalar-K} in the second coordinate.  This is the notes' layer
identity `R_{ℓ,0} = K_ℓ`.  A proof is `KernelFactor`'s optional item; the two `decide`s below
check the statement on small values. -/

set_option maxRecDepth 20000 in
/-- `K_ℓ((0,q), (0,s))` is the `d = 1` kernel `K_ℓ(q, s)` of `Av12453.OneThreshold`. -/
example : ∀ q ∈ [0, 1, 2, 3], ∀ s ∈ [0, 1, 2, 3], ∀ l ∈ [0, 1, 2, 3],
    K l (0, q) (0, s) = OneThreshold.K l q s := by decide

set_option maxRecDepth 20000 in
/-- A source control with an empty early band reaches no terminal control with a nonempty
early band. -/
example : ∀ q ∈ [0, 1, 2], ∀ s ∈ [0, 1, 2], ∀ l ∈ [0, 1, 2, 3], ∀ t1 ∈ [0, 1],
    K l (0, q) (t1 + 1, s) = 0 := by decide

/-! ### Numerical checks

The first ten values `G_{(n,0)}`, the paper's \eqref{eq:first-terms}
`1, 1, 2, 6, 24, 119, 694, 4581, 33286, 260927`; `TwoThreshold.Counting` checks the first
eight of them against a brute-force enumeration of `Av_n(12453)`.  These are `#eval`s rather
than `decide`s only because the larger values are slow to reduce in the kernel; `#guard_msgs`
makes the build fail if the output ever changes. -/

set_option linter.hashCommand false in
/-- info: [1, 1, 2, 6, 24, 119, 694, 4581, 33286, 260927] -/
#guard_msgs in
#eval (List.range 10).map (fun n => G (n, 0))

/-! The instance of \eqref{eq:factorization} promised by the brief: at the source control
`𝐩 = (1,2)`, active head `ℓ = 3` and protected tail `L = (1)`,

    H_{(1,2)}((3)(1)) = ∑_{𝐭} K_3((1,2), 𝐭) H_𝐭((1)) = 882.

The left-hand side runs the literal recurrence \eqref{eq:H} of `TwoThreshold.Defs`; the
right-hand side runs the kernel row above against the ten values `H_𝐭((1))`, `𝐭 ∈ S (1,2)`.
`KernelFactor.H_factor` proves the identity for all `𝐩`, `ℓ ≥ 1` and `L`. -/

set_option linter.hashCommand false in
/-- info: (882, 882) -/
#guard_msgs in
#eval (H (1, 2) [3, 1], ∑ t ∈ S (1, 2), K 3 (1, 2) t * H t [1])

set_option linter.hashCommand false in
/-- info: [1, 2, 6, 23, 2, 6, 24, 6, 24, 24] -/
#guard_msgs in
#eval ctrls3.map (fun t => H t [1])

end TwoThreshold
end Av12453
