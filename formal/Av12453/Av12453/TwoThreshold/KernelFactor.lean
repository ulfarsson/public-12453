/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Av12453.TwoThreshold.Kernel
import Av12453.TwoThreshold.KernelSupport

/-!
# The protected-tail factorization for `Av(12453)` (`d = 2`)

This file proves \eqref{eq:factorization} of \cref{cor:protected-tail} (section
*Protected tails and transfer kernels*, `sec:kernels`) of the paper *Protected tails and
polynomial-time enumeration of permutations avoiding a direct sum of an increasing pattern and
231*, specialized to `d = 2`: the literal recurrence
`H` of `Av12453.TwoThreshold.Defs` factors through the transfer kernel `K` of
`Av12453.TwoThreshold.Kernel`,

    H_𝐩((ℓ)L) = ∑_𝐭 K_ℓ(𝐩, 𝐭) H_𝐭(L)      (ℓ ≥ 1),

with `𝐭` running over the index set `S 𝐩 = {𝐭 : ‖𝐭‖₁ ≤ ‖𝐩‖₁}`, which carries the whole
support of the kernel row `K_ℓ(𝐩, ·)` by \cref{lem:support}
(`KernelSupport.K_eq_zero_of_mass_lt`).

The abstract protected-tail principle (`thm:protected-tail-principle`) is *not* formalized;
as at `d = 1` (`Av12453/OneThreshold/KernelFactor.lean`) the factorization is proved
directly from the defining equations of `H` and `K`, by the first-move partition that
proves \cref{prop:kernel-recurrence}.

## The proof

`Defs.H_eq_cons` (\eqref{eq:H}) and `Kernel.K_succ_eq` (\eqref{eq:K}) split the same first
move into the same **four** groups, and the induction matches them group by group.  The
induction is on the *grade* `w = ‖𝐩‖₁ + ℓ` of `sec:algorithm`, the paper's topological
order for the kernel dependencies, and it is generalized over the protected tail `L` (the
split group needs the statement at the longer tail `(b)L`); the tail is not part of the
measure, because \eqref{eq:H} and \eqref{eq:K} shrink `𝐩` and `ℓ` in lockstep and never
touch it.

* **early band** (`T_{0,h}(𝐩) = (h, p₁ + p₀ - 1 - h)`, `h < p₀`).  The successor control has
  mass `‖𝐩‖₁ - 1` and the active head is unchanged, so the term
  `H_{T_{0,h}(𝐩)}((ℓ)L)` has grade `w - 1`; the induction hypothesis rewrites it as
  `∑_{𝐭 ∈ S T_{0,h}(𝐩)} K_ℓ(T_{0,h}(𝐩), 𝐭) H_𝐭(L)`, and `KernelSupport.K_sum_extend_S`
  re-indexes that sum over `S 𝐩`.
* **last band** (`U_h(𝐩) = (p₀, h)`, `δ_h = p₁ - 1 - h`, `h < p₁`).  The successor control
  has mass `p₀ + h` and the head grows to `ℓ + δ_h`, so the grade is again
  `(p₀ + h) + (ℓ + δ_h) = w - 1` — the paper's displayed computation.  Same two steps.
* **endpoints.**  `Eend_ℓ(𝐩, L)` is `H_𝐩(L)` for `ℓ = 1`, matched against
  `D_1(𝐩, 𝐭) = 1_{𝐩 = 𝐭}` by `KernelSupport.D_one_sum`, and `2 H_𝐩((ℓ-1)L)` for `ℓ ≥ 2`,
  matched against `D_ℓ(𝐩, 𝐭) = 2 K_{ℓ-1}(𝐩, 𝐭)` by the induction hypothesis at grade
  `w - 1`.
* **splits.**  For `a + b = ℓ - 1` with `a, b ≥ 1`, two applications of the induction
  hypothesis give
  `H_𝐩((a)(b)L) = ∑_{𝐮 ∈ S 𝐩} K_a(𝐩,𝐮) H_𝐮((b)L) = ∑_𝐮 K_a(𝐩,𝐮) ∑_𝐭 K_b(𝐮,𝐭) H_𝐭(L)`
  at grades `‖𝐩‖₁ + a < w` and `‖𝐮‖₁ + b ≤ ‖𝐩‖₁ + b < w`; `Finset.sum_comm`,
  `Finset.mul_sum` and the re-indexing `S 𝐮 → S 𝐩` turn this into the split group of
  \eqref{eq:K}.

## Main results

* `H_factor` : **\eqref{eq:factorization}**, theorem 3 of the component-4b brief
(development notes, in git history).
* `H_factor_zero` : the `ℓ = 0` reading `H_𝐩(L) = ∑_{𝐭 ∈ S 𝐩} K_0(𝐩, 𝐭) H_𝐭(L)`, i.e. that
  the boundary kernel `K_0` is an identity.  Together with `H_factor` this covers every
  `ℓ ≥ 0`; it is the form \cref{cor:empty-stack-recurrence} uses for `δ_h = 0`.
* `H_factor_ctrls` : the same with the paper's own unrestricted summation range, read
  finitarily as `ctrls M` for an arbitrary `M ≥ ‖𝐩‖₁`.
* `K_eq_zero_of_fst_zero`, `K_fst_zero`, `K_layer_zero` : the cross-link with the `d = 1`
  kernel of `Av12453.OneThreshold` (theorem 6 of the brief, the notes' layer identity
  `R_{ℓ,0} = K_ℓ`): a source control with an empty early band reaches no terminal control
  with a nonempty early band, and on the layer `p₀ = t₀ = 0` the `d = 2` kernel *is* the
  `d = 1` kernel.
-/

namespace Av12453
namespace TwoThreshold

/-! ### Re-indexing a kernel row against `H`

The kernel row `K_ℓ(𝐪, ·)` is supported in `S 𝐪` (`KernelSupport.K_eq_zero_of_mass_lt`), so
for `‖𝐪‖₁ ≤ ‖𝐩‖₁` a sum of its entries against `H_·(L)` may be taken over `S 𝐩` instead.
Every group of the induction below produces a successor control `𝐪` of mass at most `‖𝐩‖₁`
and needs exactly this move; it is `KernelSupport.K_sum_extend_S` with all arguments
explicit, so that `rw` can use it without metavariables. -/

private theorem sum_S_align (q p : ℕ × ℕ) (hqp : q.1 + q.2 ≤ p.1 + p.2) (ℓ : ℕ)
    (L : List ℕ) : (∑ t ∈ S p, K ℓ q t * H t L) = ∑ t ∈ S q, K ℓ q t * H t L :=
  (K_sum_extend_S hqp ℓ fun t => H t L).symm

/-! ### The factorization -/

/-- The induction behind `H_factor`, on the grade `w = ‖𝐩‖₁ + ℓ`, generalized over the
protected tail `L`. -/
private theorem H_factor_aux : ∀ N (p : ℕ × ℕ) (ℓ : ℕ) (L : List ℕ),
    p.1 + p.2 + ℓ ≤ N → 1 ≤ ℓ →
      H p (ℓ :: L) = ∑ t ∈ S p, K ℓ p t * H t L := by
  intro N
  induction N with
  | zero => intro p ℓ L hN hℓ; omega
  | succ N ih =>
    intro p ℓ L hN hℓ
    obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
    -- the early-band group `T_{0,h}(𝐩) = (h, p₁ + p₀ - 1 - h)`
    have h1 : (∑ t ∈ S p,
          (∑ h ∈ Finset.range p.1, K (j + 1) (h, p.2 + p.1 - 1 - h) t) * H t L)
        = ∑ h ∈ Finset.range p.1, H (h, p.2 + p.1 - 1 - h) ((j + 1) :: L) := by
      calc (∑ t ∈ S p,
              (∑ h ∈ Finset.range p.1, K (j + 1) (h, p.2 + p.1 - 1 - h) t) * H t L)
          = ∑ t ∈ S p, ∑ h ∈ Finset.range p.1,
              K (j + 1) (h, p.2 + p.1 - 1 - h) t * H t L :=
            Finset.sum_congr rfl fun t _ => by rw [Finset.sum_mul]
        _ = ∑ h ∈ Finset.range p.1, ∑ t ∈ S p,
              K (j + 1) (h, p.2 + p.1 - 1 - h) t * H t L := Finset.sum_comm
        _ = ∑ h ∈ Finset.range p.1, H (h, p.2 + p.1 - 1 - h) ((j + 1) :: L) := by
            refine Finset.sum_congr rfl fun h hh => ?_
            rw [Finset.mem_range] at hh
            rw [sum_S_align (h, p.2 + p.1 - 1 - h) p
              (show h + (p.2 + p.1 - 1 - h) ≤ p.1 + p.2 by omega) (j + 1) L]
            exact (ih (h, p.2 + p.1 - 1 - h) (j + 1) L
              (show h + (p.2 + p.1 - 1 - h) + (j + 1) ≤ N by omega) (by omega)).symm
    -- the last-band group `U_h(𝐩) = (p₀, h)`, `δ_h = p₁ - 1 - h`
    have h2 : (∑ t ∈ S p,
          (∑ h ∈ Finset.range p.2, K (j + 1 + (p.2 - 1 - h)) (p.1, h) t) * H t L)
        = ∑ h ∈ Finset.range p.2, H (p.1, h) ((j + 1 + (p.2 - 1 - h)) :: L) := by
      calc (∑ t ∈ S p,
              (∑ h ∈ Finset.range p.2, K (j + 1 + (p.2 - 1 - h)) (p.1, h) t) * H t L)
          = ∑ t ∈ S p, ∑ h ∈ Finset.range p.2,
              K (j + 1 + (p.2 - 1 - h)) (p.1, h) t * H t L :=
            Finset.sum_congr rfl fun t _ => by rw [Finset.sum_mul]
        _ = ∑ h ∈ Finset.range p.2, ∑ t ∈ S p,
              K (j + 1 + (p.2 - 1 - h)) (p.1, h) t * H t L := Finset.sum_comm
        _ = ∑ h ∈ Finset.range p.2, H (p.1, h) ((j + 1 + (p.2 - 1 - h)) :: L) := by
            refine Finset.sum_congr rfl fun h hh => ?_
            rw [Finset.mem_range] at hh
            rw [sum_S_align (p.1, h) p (show p.1 + h ≤ p.1 + p.2 by omega)
              (j + 1 + (p.2 - 1 - h)) L]
            exact (ih (p.1, h) (j + 1 + (p.2 - 1 - h)) L
              (show p.1 + h + (j + 1 + (p.2 - 1 - h)) ≤ N by omega) (by omega)).symm
    -- the endpoint group
    have h3 : (∑ t ∈ S p, D (j + 1) p t * H t L) = Eend (j + 1) p L := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [Nat.zero_add, H_endpoint_one]
        exact D_one_sum p fun t => H t L
      · rw [H_endpoint_two_le (show 2 ≤ j + 1 by omega), Nat.add_sub_cancel,
          ih p j L (by omega) hj, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [D_succ (show 2 ≤ j + 1 by omega), Nat.add_sub_cancel, mul_assoc]
    -- the split group
    have h4 : (∑ t ∈ S p,
          (∑ a ∈ Finset.Ico 1 j, ∑ u ∈ S p, K a p u * K (j - a) u t) * H t L)
        = ∑ a ∈ Finset.Ico 1 j, H p (a :: (j - a) :: L) := by
      calc (∑ t ∈ S p,
              (∑ a ∈ Finset.Ico 1 j, ∑ u ∈ S p, K a p u * K (j - a) u t) * H t L)
          = ∑ t ∈ S p, ∑ a ∈ Finset.Ico 1 j,
              (∑ u ∈ S p, K a p u * K (j - a) u t) * H t L :=
            Finset.sum_congr rfl fun t _ => by rw [Finset.sum_mul]
        _ = ∑ a ∈ Finset.Ico 1 j, ∑ t ∈ S p,
              (∑ u ∈ S p, K a p u * K (j - a) u t) * H t L := Finset.sum_comm
        _ = ∑ a ∈ Finset.Ico 1 j, H p (a :: (j - a) :: L) := by
            refine Finset.sum_congr rfl fun a ha => ?_
            rw [Finset.mem_Ico] at ha
            calc (∑ t ∈ S p, (∑ u ∈ S p, K a p u * K (j - a) u t) * H t L)
                = ∑ t ∈ S p, ∑ u ∈ S p, K a p u * (K (j - a) u t * H t L) := by
                  refine Finset.sum_congr rfl fun t _ => ?_
                  rw [Finset.sum_mul]
                  exact Finset.sum_congr rfl fun u _ => by rw [mul_assoc]
              _ = ∑ u ∈ S p, ∑ t ∈ S p, K a p u * (K (j - a) u t * H t L) :=
                  Finset.sum_comm
              _ = ∑ u ∈ S p, K a p u * H u ((j - a) :: L) := by
                  refine Finset.sum_congr rfl fun u hu => ?_
                  rw [mem_S] at hu
                  rw [← Finset.mul_sum, sum_S_align u p hu (j - a) L,
                    ← ih u (j - a) L (by omega) (by omega)]
              _ = H p (a :: (j - a) :: L) :=
                  (ih p a ((j - a) :: L) (by omega) (by omega)).symm
    rw [H_eq_cons hℓ p L]
    simp only [Nat.add_sub_cancel]
    rw [← h1, ← h2, ← h3, ← h4, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [K_succ_eq hℓ p t]
    simp only [Nat.add_sub_cancel]
    ring

/-- **\eqref{eq:factorization}** (\cref{cor:protected-tail}) at `d = 2`: the protected-tail
factorization of the literal recurrence `H` of \eqref{eq:H} through the transfer kernel `K`
of \eqref{eq:K}.  The paper sums over all controls `𝐭`; the index set
`S 𝐩 = {𝐭 : ‖𝐭‖₁ ≤ ‖𝐩‖₁}` carries the whole support of `K_ℓ(𝐩, ·)` by \cref{lem:support}
(see `H_factor_ctrls` for the unrestricted reading). -/
theorem H_factor {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (p : ℕ × ℕ) (L : List ℕ) :
    H p (ℓ :: L) = ∑ t ∈ S p, K ℓ p t * H t L :=
  H_factor_aux (p.1 + p.2 + ℓ) p ℓ L le_rfl hℓ

/-- The `ℓ = 0` reading of \eqref{eq:factorization}: the boundary kernel
`K_0(𝐩, ·) = 1_{𝐩 = ·}` is an identity, so the factorization at `ℓ = 0` is the tautology
`H_𝐩(L) = H_𝐩(L)`.  Together with `H_factor` this covers every `ℓ ≥ 0`, and it is the
instance \cref{cor:empty-stack-recurrence} appeals to when `δ_h = 0`. -/
theorem H_factor_zero (p : ℕ × ℕ) (L : List ℕ) :
    H p L = ∑ t ∈ S p, K 0 p t * H t L :=
  (K_zero_sum p fun t => H t L).symm

/-- **\eqref{eq:factorization} with the paper's summation range**: the factorization may be
summed over `ctrls M` for any `M ≥ ‖𝐩‖₁`, because the row `K_ℓ(𝐩, ·)` vanishes above the
mass `‖𝐩‖₁` (`KernelSupport.K_eq_zero_of_mass_lt`).  This is the paper's `∑_𝐭`, read
finitarily. -/
theorem H_factor_ctrls {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (p : ℕ × ℕ) (L : List ℕ) {M : ℕ}
    (hM : p.1 + p.2 ≤ M) : H p (ℓ :: L) = ∑ t ∈ ctrls M, K ℓ p t * H t L := by
  rw [H_factor hℓ p L, K_sum_extend hM ℓ fun t => H t L]

/-- The `ℓ = 0` reading over `ctrls M`. -/
theorem H_factor_zero_ctrls (p : ℕ × ℕ) (L : List ℕ) {M : ℕ} (hM : p.1 + p.2 ≤ M) :
    H p L = ∑ t ∈ ctrls M, K 0 p t * H t L :=
  (K_zero_sum_ctrls hM fun t => H t L).symm

/-! ### The cross-link with the `d = 1` kernel

The controls `(0, q)` carry no early band (`T_{0,h}` ranges over `h < p₀ = 0`), so
\eqref{eq:K} at such a control is literally the `d = 1` recurrence \eqref{eq:scalar-K} in
the second coordinate.  This is theorem 6 of the component-4b brief (development notes,
in git history) and the notes'
layer identity `R_{ℓ,0} = K_ℓ`.  Two statements, proved by the same grade induction:

* `K_fst_zero` : `K_ℓ((0,q), (t₀+1, s)) = 0` — a source control with an empty early band
  reaches no terminal control with a nonempty early band.  (This is *not* a consequence of
  \cref{lem:support}, which only bounds the mass.)
* `K_layer_zero` : `K_ℓ((0,q), (0,s)) = K^{(1)}_ℓ(q, s)`, the `d = 1` kernel of
  `Av12453.OneThreshold.Kernel`.

The first is what collapses the `d = 2` split sum over `S (0,q)` to the `d = 1` split sum
over `{0, …, q}` in the proof of the second. -/

/-- The induction behind `K_eq_zero_of_fst_zero`, on the grade `w = ‖𝐩‖₁ + ℓ`. -/
private theorem K_eq_zero_of_fst_zero_aux : ∀ N ℓ (p t : ℕ × ℕ),
    p.1 + p.2 + ℓ ≤ N → p.1 = 0 → 1 ≤ t.1 → K ℓ p t = 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro ℓ p t hN hp ht
    match ℓ with
    | 0 => rw [K_zero, if_neg (by rintro rfl; omega)]
    | j + 1 =>
      rw [K_succ_eq (Nat.le_add_left 1 j) p t]
      -- the early band is empty, since `p₀ = 0`
      have hearly : (∑ h ∈ Finset.range p.1, K (j + 1) (h, p.2 + p.1 - 1 - h) t) = 0 := by
        rw [hp]; simp
      -- a last-band move keeps `p₀ = 0`
      have hlast : (∑ h ∈ Finset.range p.2, K (j + 1 + (p.2 - 1 - h)) (p.1, h) t) = 0 := by
        refine Finset.sum_eq_zero fun h hh => ?_
        rw [Finset.mem_range] at hh
        exact ih (N - 1) (by omega) (j + 1 + (p.2 - 1 - h)) (p.1, h) t
          (show p.1 + h + (j + 1 + (p.2 - 1 - h)) ≤ N - 1 by omega) hp ht
      -- an endpoint keeps the control
      have hD : D (j + 1) p t = 0 := by
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · rw [D_one, if_neg (by rintro rfl; omega)]
        · rw [D_succ (by omega) p t]
          simp only [Nat.add_sub_cancel]
          rw [ih (N - 1) (by omega) j p t (by omega) hp ht, Nat.mul_zero]
      -- in a split, either the intermediate control keeps `p₀ = 0` (and the right factor
      -- vanishes) or it does not (and the left factor vanishes)
      have hsplit : (∑ a ∈ Finset.Ico 1 (j + 1 - 1),
          ∑ u ∈ S p, K a p u * K (j + 1 - 1 - a) u t) = 0 := by
        refine Finset.sum_eq_zero fun a ha => ?_
        rw [Finset.mem_Ico] at ha
        refine Finset.sum_eq_zero fun u hu => ?_
        rw [mem_S] at hu
        rcases Nat.eq_zero_or_pos u.1 with hu1 | hu1
        · rw [ih (N - 1) (by omega) (j + 1 - 1 - a) u t (by omega) hu1 ht, Nat.mul_zero]
        · rw [ih (N - 1) (by omega) a p u (by omega) hp hu1, Nat.zero_mul]
      rw [hearly, hlast, hD, hsplit]

/-- A kernel row at a source control with an empty early band (`p₀ = 0`) vanishes at every
terminal control with a nonempty early band (`t₀ ≥ 1`). -/
theorem K_eq_zero_of_fst_zero {ℓ : ℕ} {p t : ℕ × ℕ} (hp : p.1 = 0) (ht : 1 ≤ t.1) :
    K ℓ p t = 0 :=
  K_eq_zero_of_fst_zero_aux (p.1 + p.2 + ℓ) ℓ p t le_rfl hp ht

/-- **Theorem 6, second half**: `K_ℓ((0,q), (t₀+1, s)) = 0`. -/
theorem K_fst_zero (ℓ q s t1 : ℕ) : K ℓ (0, q) (t1 + 1, s) = 0 :=
  K_eq_zero_of_fst_zero rfl (Nat.le_add_left 1 t1)

/-- Collapsing a sum over `S (0,q)` to a sum over the layer `{(0,v) : v ≤ q}`, for a
summand that vanishes off the layer.  This is how `K_fst_zero` turns the `d = 2` split sum
of \eqref{eq:K} into the `d = 1` split sum of \eqref{eq:scalar-K}. -/
private theorem sum_S_layer (q : ℕ) (f : ℕ × ℕ → ℕ)
    (hf : ∀ u ∈ S (0, q), 1 ≤ u.1 → f u = 0) :
    (∑ u ∈ S (0, q), f u) = ∑ v ∈ Finset.range (q + 1), f (0, v) := by
  have hA : (Finset.range (q + 1)).image (fun v => ((0, v) : ℕ × ℕ)) ⊆ S (0, q) := by
    intro u hu
    rw [Finset.mem_image] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    rw [Finset.mem_range] at hv
    simp only [mem_S]
    omega
  have key : (∑ u ∈ S (0, q), f u)
      = ∑ u ∈ (Finset.range (q + 1)).image (fun v => ((0, v) : ℕ × ℕ)), f u := by
    refine (Finset.sum_subset hA fun x hx hnx => ?_).symm
    obtain ⟨x1, x2⟩ := x
    simp only [mem_S] at hx
    refine hf _ (mem_S.mpr (by simpa using hx)) ?_
    rcases Nat.eq_zero_or_pos x1 with rfl | h1
    · exact absurd (Finset.mem_image.mpr
        ⟨x2, Finset.mem_range.mpr (by omega), rfl⟩) hnx
    · exact h1
  rw [key, Finset.sum_image (fun x _ y _ h => by simpa using h)]

/-- The induction behind `K_layer_zero`, on the grade `w = q + ℓ`. -/
private theorem K_layer_zero_aux : ∀ N ℓ q s, q + ℓ ≤ N →
    K ℓ (0, q) (0, s) = OneThreshold.K ℓ q s := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro ℓ q s hN
    match ℓ with
    | 0 =>
      rw [K_zero, OneThreshold.K_zero]
      by_cases h : q = s
      · subst h; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg (fun he => h (congrArg Prod.snd he)), if_neg h]
    | j + 1 =>
      -- \eqref{eq:K} at `(0, q)`, with the `Prod` projections reduced
      have hK : K (j + 1) (0, q) (0, s) =
          (∑ h ∈ Finset.range 0, K (j + 1) (h, q + 0 - 1 - h) (0, s))
            + (∑ h ∈ Finset.range q, K (j + 1 + (q - 1 - h)) (0, h) (0, s))
            + D (j + 1) (0, q) (0, s)
            + ∑ a ∈ Finset.Ico 1 (j + 1 - 1), ∑ u ∈ S (0, q),
                K a (0, q) u * K (j + 1 - 1 - a) u (0, s) :=
        K_succ_eq (Nat.le_add_left 1 j) (0, q) (0, s)
      -- the last band of \eqref{eq:K} is the base sum of \eqref{eq:scalar-K}
      have e1 : (∑ h ∈ Finset.range q, K (j + 1 + (q - 1 - h)) (0, h) (0, s))
          = ∑ h ∈ Finset.range q, OneThreshold.K (j + 1 + q - 1 - h) h s := by
        refine Finset.sum_congr rfl fun h hh => ?_
        rw [Finset.mem_range] at hh
        rw [show j + 1 + (q - 1 - h) = j + 1 + q - 1 - h from by omega]
        exact ih (N - 1) (by omega) (j + 1 + q - 1 - h) h s (by omega)
      -- the endpoint terms agree
      have e2 : D (j + 1) (0, q) (0, s) = OneThreshold.D (j + 1) q s := by
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · rw [D_one, OneThreshold.D_one]
          by_cases h : q = s
          · subst h; rw [if_pos rfl, if_pos rfl]
          · rw [if_neg (fun he => h (congrArg Prod.snd he)), if_neg h]
        · rw [D_succ (by omega), OneThreshold.D_succ (by omega)]
          simp only [Nat.add_sub_cancel]
          exact congrArg _ (ih (N - 1) (by omega) j q s (by omega))
      -- the split terms agree, once `K_fst_zero` collapses `S (0,q)` to the layer
      have e3 : ∀ a ∈ Finset.Ico 1 (j + 1 - 1),
          (∑ u ∈ S (0, q), K a (0, q) u * K (j + 1 - 1 - a) u (0, s))
            = ∑ u ∈ Finset.range (q + 1),
                OneThreshold.K a q u * OneThreshold.K (j + 1 - 1 - a) u s := by
        intro a ha
        rw [Finset.mem_Ico] at ha
        have hz : (∑ u ∈ S (0, q), K a (0, q) u * K (j + 1 - 1 - a) u (0, s))
            = ∑ v ∈ Finset.range (q + 1),
                K a (0, q) (0, v) * K (j + 1 - 1 - a) (0, v) (0, s) :=
          sum_S_layer q (fun u => K a (0, q) u * K (j + 1 - 1 - a) u (0, s))
            (fun u _ hu1 => by
              rw [show K a (0, q) u = 0 from K_eq_zero_of_fst_zero rfl hu1, Nat.zero_mul])
        rw [hz]
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [Finset.mem_range] at hv
        rw [ih (N - 1) (by omega) a q v (by omega),
          ih (N - 1) (by omega) (j + 1 - 1 - a) v s (by omega)]
      rw [hK, OneThreshold.K_succ_eq (Nat.le_add_left 1 j) q s, Finset.range_zero,
        Finset.sum_empty, Nat.zero_add, e1, e2, Finset.sum_congr rfl e3]

/-- **Theorem 6, first half** (the notes' layer identity `R_{ℓ,0} = K_ℓ`): on the layer
`p₀ = t₀ = 0` the `d = 2` transfer kernel of \eqref{eq:K} *is* the `d = 1` scalar kernel of
\eqref{eq:scalar-K}.  Both sides are defined by their own recurrences, so this is a proved
identification of the two tables, not a definitional one. -/
theorem K_layer_zero (ℓ q s : ℕ) : K ℓ (0, q) (0, s) = OneThreshold.K ℓ q s :=
  K_layer_zero_aux (q + ℓ) ℓ q s le_rfl

/-! ### Interface and sanity checks

The first two `example`s fix the statements of `H_factor` and `H_factor_zero` at compile
time: they are exactly the frozen statements of theorem 3 of
the component-4b brief (development notes, in git history)
(`TwoThreshold/KernelInterface.lean`), so any later drift in
the binders or in the index set is caught here.  The `decide` checks below evaluate both
sides of \eqref{eq:factorization} in the kernel, on protected tails of length `0`, `1` and
`2` and at four different source controls; they add no axiom. -/

/-- Statement check: `H_factor` has exactly the frozen type of theorem 3 of the brief. -/
example : ∀ {ℓ : ℕ}, 1 ≤ ℓ → ∀ (p : ℕ × ℕ) (L : List ℕ),
    H p (ℓ :: L) = ∑ t ∈ S p, K ℓ p t * H t L := @H_factor

/-- Statement check for the `ℓ = 0` reading. -/
example : ∀ (p : ℕ × ℕ) (L : List ℕ),
    H p L = ∑ t ∈ S p, K 0 p t * H t L := @H_factor_zero

/-- Statement check: the two halves of theorem 6 of the brief, in the brief's own shape. -/
example : ∀ (l q s : ℕ), K l (0, q) (0, s) = OneThreshold.K l q s := K_layer_zero

example : ∀ (l q s t1 : ℕ), K l (0, q) (t1 + 1, s) = 0 := K_fst_zero

set_option maxRecDepth 20000 in
/-- The layer identity `K_ℓ((0,q), (0,s)) = K^{(1)}_ℓ(q,s)` of `K_layer_zero`, checked
against the two evaluated tables (the same `decide` that `Kernel.lean` records). -/
example : ∀ q ∈ [0, 1, 2, 3], ∀ s ∈ [0, 1, 2, 3], ∀ l ∈ [0, 1, 2, 3],
    K l (0, q) (0, s) = OneThreshold.K l q s := by decide

set_option maxRecDepth 20000 in
/-- `K_fst_zero`, checked against the evaluated table. -/
example : ∀ q ∈ [0, 1, 2], ∀ s ∈ [0, 1, 2], ∀ l ∈ [0, 1, 2, 3], ∀ t1 ∈ [0, 1],
    K l (0, q) (t1 + 1, s) = 0 := by decide

set_option maxRecDepth 40000 in
/-- `H_{(1,2)}((3)) = ∑_{𝐭 ∈ S (1,2)} K_3((1,2), 𝐭) H_𝐭(∅)`: an empty protected tail, at the
running example's control. -/
example : H (1, 2) [3] = ∑ t ∈ S (1, 2), K 3 (1, 2) t * H t [] := by decide

set_option maxRecDepth 40000 in
/-- `H_{(1,2)}((3)(1)) = ∑_{𝐭 ∈ S (1,2)} K_3((1,2), 𝐭) H_𝐭((1)) = 882`: the instance of
\eqref{eq:factorization} that `Kernel.lean` reports by `#eval`, here proved by kernel
evaluation. -/
example : H (1, 2) [3, 1] = ∑ t ∈ S (1, 2), K 3 (1, 2) t * H t [1] := by decide

set_option maxRecDepth 40000 in
/-- A protected tail of two blocks, at the source control `(2,1)`. -/
example : H (2, 1) [2, 1, 1] = ∑ t ∈ S (2, 1), K 2 (2, 1) t * H t [1, 1] := by decide

set_option maxRecDepth 40000 in
/-- The last-band source control `(0,3)`, active head `ℓ = 1`. -/
example : H (0, 3) [1, 2] = ∑ t ∈ S (0, 3), K 1 (0, 3) t * H t [2] := by decide

set_option maxRecDepth 40000 in
/-- The early-band source control `(3,0)`, active head `ℓ = 2`. -/
example : H (3, 0) [2] = ∑ t ∈ S (3, 0), K 2 (3, 0) t * H t [] := by decide

set_option maxRecDepth 40000 in
/-- The `ℓ = 0` reading at `𝐩 = (2,2)`, `L = (2)(1)`. -/
example : H (2, 2) [2, 1] = ∑ t ∈ S (2, 2), K 0 (2, 2) t * H t [2, 1] := by decide

end TwoThreshold
end Av12453
