/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Av12453.TwoThreshold.Kernel

/-!
# Support of the two-threshold kernel rows

This file proves \cref{lem:support} (*Kernel support*) of the section *The family algorithm
and its complexity* (`sec:algorithm`) of the paper *Protected tails and polynomial-time
enumeration of permutations avoiding a direct sum of an increasing pattern and 231*,
specialized to `d = 2`, together with the range-extension
lemmas that the two phase-2 modules (`KernelFactor.lean`, `KernelCount.lean`) need in order
to align the truncated index sets of `Kernel.lean` with each other and with the paper's
unrestricted sums.

The kernel `K`, its defining equations `K_zero`, `K_succ_eq`, `D_eq`, `D_one`, `D_succ` and
the empty-stack values `G` are `Av12453.TwoThreshold.Kernel`; nothing here uses the literal
recurrence `H` of `Av12453.TwoThreshold.Defs`, so this file is about the kernel table alone.

## The two support statements

Write `‖𝐩‖₁ = p₀ + p₁` for the mass of a control and `w = ‖𝐩‖₁ + ℓ` for the grade of a
kernel source, the topological order of \eqref{eq:K} that `Kernel.lean` uses as its fuel.

* `K_eq_zero_of_mass_lt` : `‖𝐩‖₁ < ‖𝐭‖₁ → K_ℓ(𝐩, 𝐭) = 0`, for **every** `ℓ`, including
  `ℓ = 0`.  This is the mass half of \cref{lem:support}: no path from control `𝐩` can reach
  a terminal control of larger mass, because a base move consumes a letter and lowers the
  mass while an active-interval move leaves the control unchanged.  Formally it is a strong
  induction on the grade: an early-band term of \eqref{eq:K} has source mass `‖𝐩‖₁ - 1` and
  grade `w - 1`; a last-band term has source mass `p₀ + h ≤ ‖𝐩‖₁ - 1` and grade `w - 1`;
  `D_ℓ` is either `1_{𝐩 = 𝐭} = 0` or `2 K_{ℓ-1}(𝐩, 𝐭)` at grade `w - 1`; and in a split term
  `K_a(𝐩, 𝐮) K_b(𝐮, 𝐭)` the right factor has source mass `‖𝐮‖₁ ≤ ‖𝐩‖₁ < ‖𝐭‖₁` (the index
  set `S 𝐩` truncates `𝐮`) and grade `‖𝐮‖₁ + b ≤ w - 2`.

  This is the theorem that justifies the two deviations from the paper's display recorded in
  `Kernel.lean`: the split sum of \eqref{eq:K} and the inner sum of \eqref{eq:G} are taken
  over the finite sets `S 𝐩` and `S (p₀, h)` rather than over all controls.
  `K_succ_eq_ctrls` and `G_eq_ctrls` below make that statement formal.

* `K_support` : \eqref{eq:support} itself, `supp K_ℓ(𝐩, ·) ⊆ {𝐩} ∪ {𝐭 : ‖𝐭‖₁ ≤ ‖𝐩‖₁ - 1}`
  for `ℓ ≥ 1`, in the contrapositive-free form `K_ℓ(𝐩, 𝐭) ≠ 0 → 𝐭 = 𝐩 ∨ ‖𝐭‖₁ + 1 ≤ ‖𝐩‖₁`.
  The proof is the same strong induction on the grade, run on the contrapositive
  (`𝐭 ≠ 𝐩` and `‖𝐩‖₁ ≤ ‖𝐭‖₁` force `K_ℓ(𝐩, 𝐭) = 0`): the two band groups drop the source
  mass below `‖𝐭‖₁` and vanish by `K_eq_zero_of_mass_lt`; `D_1` is `1_{𝐩=𝐭} = 0` and `D_ℓ`
  recurses at grade `w - 1` with the same controls; and a split term
  `K_a(𝐩, 𝐮) K_b(𝐮, 𝐭)` (with `a, b ≥ 1`) vanishes in each of three cases -- if
  `‖𝐮‖₁ < ‖𝐩‖₁` the right factor vanishes by `K_eq_zero_of_mass_lt`, if `𝐮 = 𝐩` the right
  factor vanishes by the induction hypothesis, and otherwise (`𝐮 ≠ 𝐩` and `‖𝐩‖₁ ≤ ‖𝐮‖₁`)
  the left factor vanishes by the induction hypothesis.  That case split is exactly the
  paper's "if no base move occurs the terminal control is `𝐩`, and if at least one base move
  occurs the terminal control has mass at most `‖𝐩‖₁ - 1`", composed along a split.

## Main results

* `K_eq_zero_of_mass_lt`, `K_support` : \cref{lem:support}, theorems 1 and 2 of
  the component-4b brief (development notes, in git history).
* `K_eq_zero_of_not_mem_S`, `mem_S_of_K_ne_zero` : the same bound phrased through `S 𝐩`.
* `K_sum_extend`, `K_sum_extend_left` and their `S`-to-`S` and general-`Finset` variants: a
  sum against the kernel row `K_ℓ(𝐩, ·)` may be taken over any finite set of controls
  containing `S 𝐩`, because the omitted summands vanish.  These are what let a phase-2 proof
  align a sum over `S 𝐩'` (for a control `𝐩'` of smaller mass, produced by a band move or by
  a split) with a sum over `S 𝐩`.
* `self_mem_ctrls`, `self_mem_S`, `sum_S_ite`, `K_zero_sum`, `D_one_sum`, `sum_ctrls_ite`,
  `K_zero_sum_ctrls` : the `Finset` facts about the index sets that phase 2 needs, in
  particular that an indicator `1_{𝐩 = ·}` sums out of a sum over `S 𝐩` -- which is how the
  boundary kernel `K_0` acts as the identity (\cref{cor:empty-stack-recurrence}'s "the
  identity kernel `K_0` handles `δ_h = 0`", and the `ℓ = 0` reading of
  \eqref{eq:factorization}) and how the endpoint term `D_1` acts in the endpoint group of
  \eqref{eq:K}.
* `K_succ_eq_ctrls`, `G_eq_ctrls` : \eqref{eq:K} and \eqref{eq:G} with their control sums
  taken over an arbitrary `ctrls M` large enough to contain the support -- the finitary
  reading of the paper's unrestricted `∑_𝐮` and `∑_𝐭`.
-/

namespace Av12453
namespace TwoThreshold

/-! ### Theorem 1: a kernel row vanishes above the mass of its source control -/

/-- The induction behind `K_eq_zero_of_mass_lt`, on the grade `w = ‖𝐩‖₁ + ℓ`. -/
private theorem K_eq_zero_of_mass_lt_aux : ∀ N ℓ (p t : ℕ × ℕ),
    p.1 + p.2 + ℓ ≤ N → p.1 + p.2 < t.1 + t.2 → K ℓ p t = 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro ℓ p t hN hpt
    match ℓ with
    | 0 => rw [K_zero, if_neg (by rintro rfl; omega)]
    | j + 1 =>
      rw [K_succ_eq (Nat.le_add_left 1 j) p t]
      /- Early band: source control `T_{0,h}(𝐩) = (h, p₁ + p₀ - 1 - h)` of mass `‖𝐩‖₁ - 1`,
      grade `w - 1`. -/
      have hearly : (∑ h ∈ Finset.range p.1, K (j + 1) (h, p.2 + p.1 - 1 - h) t) = 0 := by
        refine Finset.sum_eq_zero fun h hh => ?_
        rw [Finset.mem_range] at hh
        exact ih (N - 1) (by omega) (j + 1) (h, p.2 + p.1 - 1 - h) t
          (show h + (p.2 + p.1 - 1 - h) + (j + 1) ≤ N - 1 by omega)
          (show h + (p.2 + p.1 - 1 - h) < t.1 + t.2 by omega)
      /- Last band: source control `U_h(𝐩) = (p₀, h)` of mass `p₀ + h ≤ ‖𝐩‖₁ - 1`, grade
      `(p₀ + h) + (ℓ + δ_h) = w - 1`. -/
      have hlast : (∑ h ∈ Finset.range p.2, K (j + 1 + (p.2 - 1 - h)) (p.1, h) t) = 0 := by
        refine Finset.sum_eq_zero fun h hh => ?_
        rw [Finset.mem_range] at hh
        exact ih (N - 1) (by omega) (j + 1 + (p.2 - 1 - h)) (p.1, h) t
          (show p.1 + h + (j + 1 + (p.2 - 1 - h)) ≤ N - 1 by omega)
          (show p.1 + h < t.1 + t.2 by omega)
      /- Endpoints: `D_1 = 1_{𝐩 = 𝐭} = 0`, and `D_ℓ = 2 K_{ℓ-1}(𝐩, 𝐭)` at grade `w - 1`. -/
      have hD : D (j + 1) p t = 0 := by
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · rw [D_one, if_neg (by rintro rfl; omega)]
        · rw [D_succ (by omega) p t]
          simp only [Nat.add_sub_cancel]
          rw [ih (N - 1) (by omega) j p t (by omega) hpt, Nat.mul_zero]
      /- Splits: the right factor has source `𝐮` with `‖𝐮‖₁ ≤ ‖𝐩‖₁ < ‖𝐭‖₁` and grade
      `‖𝐮‖₁ + (ℓ - 1 - a) ≤ w - 2`. -/
      have hsplit : (∑ a ∈ Finset.Ico 1 (j + 1 - 1),
          ∑ u ∈ S p, K a p u * K (j + 1 - 1 - a) u t) = 0 := by
        refine Finset.sum_eq_zero fun a ha => ?_
        rw [Finset.mem_Ico] at ha
        refine Finset.sum_eq_zero fun u hu => ?_
        rw [mem_S] at hu
        rw [ih (N - 1) (by omega) (j + 1 - 1 - a) u t (by omega) (by omega), Nat.mul_zero]
      rw [hearly, hlast, hD, hsplit]

/-- **\cref{lem:support}, the mass half**: a kernel row `K_ℓ(𝐩, ·)` vanishes at every
terminal control of mass strictly larger than `‖𝐩‖₁`, for every `ℓ` (including `ℓ = 0`,
where it is the statement that `𝐩 ≠ 𝐭`).  The paper's reason is that every base move
strictly lowers the control mass and every active-interval move leaves the control
unchanged, so no stopped path from `𝐩` reaches a control of larger mass.

This is the theorem that justifies the truncated index sets `S 𝐩` and `S (p₀, h)` used in
`Kernel.K_succ_eq` and `Kernel.G_eq`: see `K_succ_eq_ctrls` and `G_eq_ctrls`. -/
theorem K_eq_zero_of_mass_lt {ℓ : ℕ} {p t : ℕ × ℕ} (h : p.1 + p.2 < t.1 + t.2) :
    K ℓ p t = 0 :=
  K_eq_zero_of_mass_lt_aux (p.1 + p.2 + ℓ) ℓ p t le_rfl h

/-! ### Theorem 2: the support bound \eqref{eq:support} -/

/-- The induction behind `K_support`, on the grade `w = ‖𝐩‖₁ + ℓ`, in contrapositive form:
a row entry outside `{𝐩} ∪ {𝐭 : ‖𝐭‖₁ < ‖𝐩‖₁}` is zero. -/
private theorem K_support_aux : ∀ N ℓ (p t : ℕ × ℕ),
    p.1 + p.2 + ℓ ≤ N → 1 ≤ ℓ → t ≠ p → p.1 + p.2 ≤ t.1 + t.2 → K ℓ p t = 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro ℓ p t hN hℓ hne hmass
    obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
    rw [K_succ_eq (Nat.le_add_left 1 j) p t]
    /- Both band groups lower the source mass strictly below `‖𝐭‖₁`, so they vanish by
    theorem 1 -- this is the paper's "at least one base move occurred". -/
    have hearly : (∑ h ∈ Finset.range p.1, K (j + 1) (h, p.2 + p.1 - 1 - h) t) = 0 := by
      refine Finset.sum_eq_zero fun h hh => ?_
      rw [Finset.mem_range] at hh
      exact K_eq_zero_of_mass_lt (show h + (p.2 + p.1 - 1 - h) < t.1 + t.2 by omega)
    have hlast : (∑ h ∈ Finset.range p.2, K (j + 1 + (p.2 - 1 - h)) (p.1, h) t) = 0 := by
      refine Finset.sum_eq_zero fun h hh => ?_
      rw [Finset.mem_range] at hh
      exact K_eq_zero_of_mass_lt (show p.1 + h < t.1 + t.2 by omega)
    /- Endpoints keep the control: `D_1 = 1_{𝐩 = 𝐭} = 0` since `𝐭 ≠ 𝐩`, and `D_ℓ` recurses
    at grade `w - 1` with the same `𝐩` and `𝐭`. -/
    have hD : D (j + 1) p t = 0 := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [D_one, if_neg hne.symm]
      · rw [D_succ (by omega) p t]
        simp only [Nat.add_sub_cancel]
        rw [ih (N - 1) (by omega) j p t (by omega) (by omega) hne hmass, Nat.mul_zero]
    /- A split `K_a(𝐩, 𝐮) K_b(𝐮, 𝐭)` with `a, b ≥ 1`: three cases. -/
    have hsplit : (∑ a ∈ Finset.Ico 1 (j + 1 - 1),
        ∑ u ∈ S p, K a p u * K (j + 1 - 1 - a) u t) = 0 := by
      refine Finset.sum_eq_zero fun a ha => ?_
      rw [Finset.mem_Ico] at ha
      refine Finset.sum_eq_zero fun u hu => ?_
      rw [mem_S] at hu
      by_cases hum : u.1 + u.2 < p.1 + p.2
      · -- the intermediate control already lost mass: the right factor vanishes (theorem 1)
        rw [K_eq_zero_of_mass_lt (show u.1 + u.2 < t.1 + t.2 by omega), Nat.mul_zero]
      · by_cases hup : u = p
        · -- no mass was lost before the cut: the right factor is a row at `𝐩` again
          rw [hup, ih (N - 1) (by omega) (j + 1 - 1 - a) p t (by omega) (by omega) hne hmass,
            Nat.mul_zero]
        · -- the intermediate control is a *different* control of mass at least `‖𝐩‖₁`
          rw [ih (N - 1) (by omega) a p u (by omega) (by omega) hup (by omega), Nat.zero_mul]
    rw [hearly, hlast, hD, hsplit]

/-- **\eqref{eq:support}** (\cref{lem:support}): for `ℓ ≥ 1`,
`supp K_ℓ(𝐩, ·) ⊆ {𝐩} ∪ {𝐭 : ‖𝐭‖₁ ≤ ‖𝐩‖₁ - 1}`.  A stopped path either makes no base move,
and then ends at the source control `𝐩`, or makes at least one, and then ends at a control
of mass at most `‖𝐩‖₁ - 1`. -/
theorem K_support {ℓ : ℕ} {p t : ℕ × ℕ} (hℓ : 1 ≤ ℓ) (h : K ℓ p t ≠ 0) :
    t = p ∨ t.1 + t.2 + 1 ≤ p.1 + p.2 := by
  by_contra hc
  have hne : t ≠ p := fun he => hc (Or.inl he)
  have hmass : p.1 + p.2 ≤ t.1 + t.2 := by
    by_contra hm
    exact hc (Or.inr (by omega))
  exact h (K_support_aux (p.1 + p.2 + ℓ) ℓ p t le_rfl hℓ hne hmass)

/-! ### The support through the index set `S 𝐩`, and range extension

`Kernel.lean` truncates the paper's sums over all controls to the finite sets
`S 𝐩 = ctrls ‖𝐩‖₁` and `ctrls M`.  The lemmas below are the interface to that truncation:
a kernel row vanishes off `S 𝐩` (`K_eq_zero_of_not_mem_S`), so a sum against it may be taken
over any finite set of controls containing `S 𝐩` (`K_sum_extend*`).  Phase 2 uses this to
align a sum over `S 𝐩'`, for a control `𝐩'` of smaller mass produced by a band move or by a
split, with a sum over `S 𝐩`. -/

/-- A kernel row vanishes outside the index set `S 𝐩` attached to its source control. -/
theorem K_eq_zero_of_not_mem_S {ℓ : ℕ} {p t : ℕ × ℕ} (h : t ∉ S p) : K ℓ p t = 0 :=
  K_eq_zero_of_mass_lt (by simp only [mem_S] at h; omega)

/-- Contrapositive of `K_eq_zero_of_not_mem_S`: the support of a kernel row is contained in
`S 𝐩`. -/
theorem mem_S_of_K_ne_zero {ℓ : ℕ} {p t : ℕ × ℕ} (h : K ℓ p t ≠ 0) : t ∈ S p := by
  by_contra hc
  exact h (K_eq_zero_of_not_mem_S hc)

/-- Every control belongs to `ctrls M` as soon as `M` bounds its mass. -/
theorem self_mem_ctrls {p : ℕ × ℕ} {M : ℕ} (h : p.1 + p.2 ≤ M) : p ∈ ctrls M :=
  mem_ctrls.mpr h

/-- A source control belongs to its own index set. -/
theorem self_mem_S (p : ℕ × ℕ) : p ∈ S p := mem_S.mpr le_rfl

/-- **Range extension**, general form: a sum of `K ℓ 𝐩 𝐭 * f 𝐭` over `S 𝐩` may be taken over
any larger finite set of controls, since the omitted summands vanish. -/
theorem K_sum_extend_subset {p : ℕ × ℕ} {A : Finset (ℕ × ℕ)} (hA : S p ⊆ A) (ℓ : ℕ)
    (f : ℕ × ℕ → ℕ) : (∑ t ∈ S p, K ℓ p t * f t) = ∑ t ∈ A, K ℓ p t * f t := by
  refine Finset.sum_subset hA fun t _ ht => ?_
  rw [K_eq_zero_of_not_mem_S ht, Nat.zero_mul]

/-- **Range extension**, general form, with the kernel on the right of the product. -/
theorem K_sum_extend_subset_left {p : ℕ × ℕ} {A : Finset (ℕ × ℕ)} (hA : S p ⊆ A) (ℓ : ℕ)
    (f : ℕ × ℕ → ℕ) : (∑ t ∈ S p, f t * K ℓ p t) = ∑ t ∈ A, f t * K ℓ p t := by
  refine Finset.sum_subset hA fun t _ ht => ?_
  rw [K_eq_zero_of_not_mem_S ht, Nat.mul_zero]

/-- **Range extension** to `ctrls M`: for `‖𝐩‖₁ ≤ M`, a sum of `K ℓ 𝐩 𝐭 * f 𝐭` over the
index set `S 𝐩` of `Kernel.lean` equals the sum over all controls of mass at most `M`. -/
theorem K_sum_extend {p : ℕ × ℕ} {M : ℕ} (hM : p.1 + p.2 ≤ M) (ℓ : ℕ) (f : ℕ × ℕ → ℕ) :
    (∑ t ∈ S p, K ℓ p t * f t) = ∑ t ∈ ctrls M, K ℓ p t * f t :=
  K_sum_extend_subset (S_subset_ctrls hM) ℓ f

/-- `K_sum_extend` with the kernel on the right of the product, as it occurs in the split
terms of \eqref{eq:K}. -/
theorem K_sum_extend_left {p : ℕ × ℕ} {M : ℕ} (hM : p.1 + p.2 ≤ M) (ℓ : ℕ)
    (f : ℕ × ℕ → ℕ) : (∑ t ∈ S p, f t * K ℓ p t) = ∑ t ∈ ctrls M, f t * K ℓ p t :=
  K_sum_extend_subset_left (S_subset_ctrls hM) ℓ f

/-- **Range extension** from one index set to another: a row at a control `𝐩` of mass at
most `‖𝐪‖₁` may be summed over `S 𝐪`.  This is the form phase 2 uses, with `𝐩` a band or
split successor of `𝐪`. -/
theorem K_sum_extend_S {p q : ℕ × ℕ} (h : p.1 + p.2 ≤ q.1 + q.2) (ℓ : ℕ) (f : ℕ × ℕ → ℕ) :
    (∑ t ∈ S p, K ℓ p t * f t) = ∑ t ∈ S q, K ℓ p t * f t :=
  K_sum_extend_subset (S_mono h) ℓ f

/-- `K_sum_extend_S` with the kernel on the right of the product. -/
theorem K_sum_extend_S_left {p q : ℕ × ℕ} (h : p.1 + p.2 ≤ q.1 + q.2) (ℓ : ℕ)
    (f : ℕ × ℕ → ℕ) : (∑ t ∈ S p, f t * K ℓ p t) = ∑ t ∈ S q, f t * K ℓ p t :=
  K_sum_extend_subset_left (S_mono h) ℓ f

/-! ### The boundary kernel as an identity

`K_0(𝐩, ·) = 1_{𝐩 = ·}` is the identity kernel of the paper, used in
\cref{cor:empty-stack-recurrence} to cover `δ_h = 0` and in the `ℓ = 0` reading of
\eqref{eq:factorization}. -/

/-- **An indicator sums out of a sum over `S 𝐩`**: `∑_{𝐭 ∈ S 𝐩} 1_{𝐩 = 𝐭} f(𝐭) = f(𝐩)`.
Both `K_0(𝐩, ·)` (`Kernel.K_zero`) and `D_1(𝐩, ·)` (`Kernel.D_one`) are this indicator. -/
theorem sum_S_ite (p : ℕ × ℕ) (f : ℕ × ℕ → ℕ) :
    (∑ t ∈ S p, (if p = t then 1 else 0) * f t) = f p := by
  rw [Finset.sum_eq_single p
      (fun t _ hne => by rw [if_neg hne.symm, Nat.zero_mul])
      (fun hp => absurd (self_mem_S p) hp),
    if_pos rfl, Nat.one_mul]

/-- **The boundary kernel is an identity against any sum over `S 𝐩`**:
`∑_{𝐭 ∈ S 𝐩} K_0(𝐩, 𝐭) f(𝐭) = f(𝐩)`. -/
theorem K_zero_sum (p : ℕ × ℕ) (f : ℕ × ℕ → ℕ) : (∑ t ∈ S p, K 0 p t * f t) = f p := by
  simp only [K_zero]
  exact sum_S_ite p f

/-- **The endpoint term `D_1` is an identity against any sum over `S 𝐩`**, the shape in
which the indicator occurs in the endpoint group of \eqref{eq:K} at `ℓ = 1`. -/
theorem D_one_sum (p : ℕ × ℕ) (f : ℕ × ℕ → ℕ) : (∑ t ∈ S p, D 1 p t * f t) = f p := by
  simp only [D_one]
  exact sum_S_ite p f

/-- `sum_S_ite` over `ctrls M` for any `M` bounding `‖𝐩‖₁`. -/
theorem sum_ctrls_ite {p : ℕ × ℕ} {M : ℕ} (hM : p.1 + p.2 ≤ M) (f : ℕ × ℕ → ℕ) :
    (∑ t ∈ ctrls M, (if p = t then 1 else 0) * f t) = f p := by
  rw [← sum_S_ite p f]
  refine (Finset.sum_subset (S_subset_ctrls hM) fun t _ ht => ?_).symm
  have hne : p ≠ t := by rintro rfl; exact ht (self_mem_S _)
  rw [if_neg hne, Nat.zero_mul]

/-- `K_zero_sum` over `ctrls M` for any `M` bounding `‖𝐩‖₁`. -/
theorem K_zero_sum_ctrls {p : ℕ × ℕ} {M : ℕ} (hM : p.1 + p.2 ≤ M) (f : ℕ × ℕ → ℕ) :
    (∑ t ∈ ctrls M, K 0 p t * f t) = f p := by
  rw [← K_sum_extend hM 0 f, K_zero_sum]

/-! ### The paper's unrestricted sums

\eqref{eq:K} sums the split term over *all* controls `𝐮` and \eqref{eq:G} sums `𝐭` over
*all* controls, whereas `Kernel.K_succ_eq` and `Kernel.G_eq` use the truncated index sets
`S 𝐩` and `S (p₀, h)` -- the truncation being what makes the recursion terminate on the
grade before a support lemma is available.  The two lemmas below record that the truncation
is exactly the support restriction of `K_eq_zero_of_mass_lt`: the same equations hold with
the control sums taken over `ctrls M` for *any* `M` large enough, so nothing is lost.
(`ctrls M` with `M` arbitrary is the finitary reading of the paper's `∑_𝐮` and `∑_𝐭`: all
but finitely many summands vanish.) -/

/-- **\eqref{eq:K} with the paper's summation range**: the split term of the kernel
recurrence may be summed over `ctrls M` for any `M ≥ ‖𝐩‖₁`, because `K_a(𝐩, 𝐮) = 0` once
`‖𝐮‖₁ > ‖𝐩‖₁`. -/
theorem K_succ_eq_ctrls {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (p t : ℕ × ℕ) {M : ℕ} (hM : p.1 + p.2 ≤ M) :
    K ℓ p t =
      (∑ h ∈ Finset.range p.1, K ℓ (h, p.2 + p.1 - 1 - h) t)
        + (∑ h ∈ Finset.range p.2, K (ℓ + (p.2 - 1 - h)) (p.1, h) t)
        + D ℓ p t
        + ∑ a ∈ Finset.Ico 1 (ℓ - 1), ∑ u ∈ ctrls M, K a p u * K (ℓ - 1 - a) u t := by
  rw [K_succ_eq hℓ p t]
  congr 1
  exact Finset.sum_congr rfl fun a _ => K_sum_extend hM a (fun u => K (ℓ - 1 - a) u t)

/-- **\eqref{eq:G} with the paper's summation range**: the inner sum over terminal controls
may be taken over `ctrls M` for any `M ≥ ‖𝐩‖₁`, because the row `K_{δ_h}(U_h(𝐩), ·)`
vanishes above the mass `p₀ + h < ‖𝐩‖₁` of its source control. -/
theorem G_eq_ctrls (p : ℕ × ℕ) {M : ℕ} (hM : p.1 + p.2 ≤ M) :
    G p = (if p = (0, 0) then 1 else 0)
      + (∑ h ∈ Finset.range p.1, G (h, p.2 + p.1 - 1 - h))
      + ∑ h ∈ Finset.range p.2, ∑ t ∈ ctrls M, K (p.2 - 1 - h) (p.1, h) t * G t := by
  rw [G_eq p]
  congr 1
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.mem_range] at hh
  exact K_sum_extend (p := (p.1, h)) (show p.1 + h ≤ M by omega) (p.2 - 1 - h) G

/-! ### Cross-checks

`Kernel.lean` computes the two running-example rows `K_3((1,2), ·)` and `K_1((4,0), ·)` and
observes their support by `decide`; the same vanishing statements are re-derived here from
the two theorems, so that the support bound is checked against the evaluated table rather
than only asserted. -/

example : K 3 (1, 2) (2, 2) = 0 := K_eq_zero_of_mass_lt (by omega)

example : K 1 (4, 0) (0, 5) = 0 := K_eq_zero_of_mass_lt (by omega)

/-- `K_1((4,0), (0,4)) = 0`: the terminal control has the *same* mass as the source control
but is a different control, so `K_eq_zero_of_mass_lt` does not apply and \eqref{eq:support}
is needed. -/
example : K 1 (4, 0) (0, 4) = 0 := by
  by_contra h
  rcases K_support (le_refl 1) h with h1 | h1
  · exact absurd h1 (by decide)
  · omega

/-- The support bound is sharp at the source control: `K_3((1,2), (1,2)) ≠ 0`, and indeed
the only terminal control of mass `3` in the row is `(1,2)` itself. -/
example : K 3 (1, 2) (1, 2) ≠ 0 := by decide

end TwoThreshold
end Av12453
