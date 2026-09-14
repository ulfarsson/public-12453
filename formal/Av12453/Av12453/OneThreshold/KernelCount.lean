/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Av12453.OneThreshold.Kernel
import Av12453.OneThreshold.KernelSupport
import Av12453.OneThreshold.KernelFactor
import Av12453.OneThreshold.Counting

/-!
# Component 4a, theorems 5 and 6: the kernel algorithm counts `1342`-avoiders

This module closes the `d = 1` kernel algorithm of the subsection *The scalar kernel
algorithm* of Section 2 of the paper *Protected tails and polynomial-time enumeration of
permutations avoiding a direct sum of an increasing pattern and 231*: the numbers `G p`
computed from the kernel table `K` by \eqref{eq:scalar-G} agree
with the literal recurrence `W` at the empty stack, and therefore count `1342`-avoiding
permutations.

The single input from outside is the protected-tail factorization
\eqref{eq:scalar-factorization},

    W p (ℓ :: L) = ∑ t ≤ p, K ℓ p t * W t L        (ℓ ≥ 1),

which is theorem 4 of the component-4a brief (development notes, in git history) (`W_factor`,
phase 2b,
`KernelFactor.lean`).  It enters here only as the explicit hypothesis `hF` of
`G_eq_W_of`/`av1342_count_kernel_of`, so that both theorems are axiom-clean; the
integrator discharges it with `W_factor` (see the note at the end of this docstring).

## The proof

Strong induction on `p`.  The two recurrences

* `G_eq`      : `G p = 1_{p = 0} + ∑_{h < p} ∑_{t ≤ h} K_{p-1-h}(h, t) G_t`, and
* `W_eq_nil`  : `W p ∅ = 1_{p = 0} + ∑_{h < p} W_h (nz [p-1-h])`

have the same indicator and the same index set `h ∈ {0, …, p-1}`, so it suffices to match
the two summands at each `h`.  The induction hypothesis replaces `G t` by `W t ∅` for every
`t ≤ h < p`, which leaves

    ∑_{t ≤ h} K_{p-1-h}(h, t) W_t(∅) = W_h (nz [p-1-h]).

Write `ℓ = p - 1 - h` for the size of the interval created by the base move to the letter
with `h` unread letters below it (`W_eq_nil` is \eqref{eq:W-boundary}).

* If `ℓ ≥ 1` the created interval is nonempty, `nz [ℓ] = [ℓ]`, and the identity is exactly
  \eqref{eq:scalar-factorization} at the empty tail `L = ∅`, i.e. `hF ℓ h [] hℓ`.
* If `ℓ = 0` -- the case `h = p - 1`, where the new minimum is the letter directly below
  the old one and no interval is created -- then `nz [0] = []` and the identity is the
  paper's remark that "`K₀` covers the case `h = p-1`": the identity kernel
  `K 0 h t = 1_{h = t}` collapses the sum to its `t = h` term, `W h ∅`.

The paper's `∑_{t ≥ 0}` in \eqref{eq:scalar-G} and \eqref{eq:scalar-factorization} is the
finite `∑_{t ≤ p}` of `G_eq` and of `hF` here; the two ranges agree by the upper half of
\cref{lem:scalar-support} (`K_eq_zero_of_lt`, theorem 1), which is carried along as the
hypothesis `hK0` for interface compatibility.  Because `G_eq` and `hF` are *already* stated
on the truncated range `{0, …, p}`, and because those two ranges coincide (both are
`Finset.range (h + 1)` at the base move to `h`), the argument below never has to extend a
range: `hK0` is not used in the proof.  It is kept in the signature so that the frozen
interface of the brief is respected and so that the integrator may supply it uniformly.

## Main results

* `G_eq_W_of` : **theorem 5**, `G p = W p ∅`, relative to the factorization `hF`.
* `G_eq_W` : **theorem 5** with `hF` and `hK0` discharged by `KernelFactor.W_factor` and
  `KernelSupport.K_eq_zero_of_lt`.
* `av1342_count_kernel_of` : **theorem 6 and the goal of component 4a**,
  `G n = |Av_n(1342)|`, relative to `hF`, from `G_eq_W_of` and
  `Av12453.OneThreshold.av1342_count`.
* `av1342_count_kernel` : **the goal of component 4a**, unconditionally.
* `G_four_kernel_rows`, `G_zero`, `G_one`, `G_two`, `G_three`, `G_four` : the arithmetic of
  \cref{ex:scalar-kernel}, *From kernel rows to `|Av₄(1342)|`*, derived from `G_eq` and the
  three kernel rows.

## Integration (phase 3)

`W_factor` (theorem 4, `KernelFactor.lean`) and `K_eq_zero_of_lt` (theorem 1,
`KernelSupport.lean`) are now imported, so the two hypotheses are discharged here and the
unconditional `G_eq_W` and `av1342_count_kernel` are stated below, immediately after the
`_of` forms whose proofs they reuse verbatim.  The scaffolding module
`KernelInterface.lean`, which held the six frozen placeholder statements of phase 1, has been
deleted.
-/

namespace Av12453
namespace OneThreshold

/-! ### The hypotheses

`ScalarFactorization` is \eqref{eq:scalar-factorization} and `KernelSupportUpper` is the
upper half of \cref{lem:scalar-support}; they are theorems 4 and 1 of the brief, proved in
the sibling modules `KernelFactor.lean` and `KernelSupport.lean`.  Stating them as
hypotheses keeps this module independent of those proofs. -/

/-- **\eqref{eq:scalar-factorization}** as a hypothesis: the protected-tail factorization of
the literal recurrence `W` through the scalar kernel `K`.  Discharged by `W_factor`. -/
def ScalarFactorization : Prop :=
  ∀ (ℓ p : ℕ) (L : List ℕ), 1 ≤ ℓ →
    W p (ℓ :: L) = ∑ t ∈ Finset.range (p + 1), K ℓ p t * W t L

/-- **\cref{lem:scalar-support}, upper half** as a hypothesis: a kernel row `K_ℓ(p, ·)`
vanishes above its source control.  Discharged by `K_eq_zero_of_lt`. -/
def KernelSupportUpper : Prop := ∀ ℓ p t : ℕ, p < t → K ℓ p t = 0

/-! ### Theorem 5: the kernel values are the empty-stack values -/

set_option linter.unusedVariables false in
/--
**Theorem 5** (\eqref{eq:scalar-G}, first half): the empty-stack values `G_p` computed from
the kernel table alone agree with the literal one-threshold recurrence at the empty stack,
`G_p = W_p(∅)`.

Relative to the factorization `hF` (\eqref{eq:scalar-factorization}, theorem 4) and, for
interface compatibility only, the support bound `hK0` (\cref{lem:scalar-support}, theorem
1); `hK0` is not needed, because `G_eq` and `hF` are both already stated on the truncated
range `Finset.range (p + 1)`.
-/
theorem G_eq_W_of (hF : ScalarFactorization) (hK0 : KernelSupportUpper) :
    ∀ p : ℕ, G p = W p [] := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    -- The two recurrences have the same indicator and the same outer index set.
    rw [G_eq p, W_eq_nil p]
    refine congrArg _ (Finset.sum_congr rfl fun h hh => ?_)
    rw [Finset.mem_range] at hh
    -- Induction hypothesis: `G t = W t ∅` for every `t ≤ h < p`.
    have hG : ∀ t ∈ Finset.range (h + 1),
        K (p - 1 - h) h t * G t = K (p - 1 - h) h t * W t [] := by
      intro t ht
      rw [Finset.mem_range] at ht
      rw [ih t (by omega)]
    rw [Finset.sum_congr rfl hG]
    -- `ℓ = p - 1 - h` is the size of the interval created by the base move.
    rcases Nat.eq_zero_or_pos (p - 1 - h) with hz | hpos
    · -- `ℓ = 0` (the case `h = p - 1`): no interval is created and `K₀` collapses the sum.
      rw [hz, nz_singleton, if_pos rfl]
      have hid : ∀ t ∈ Finset.range (h + 1),
          K 0 h t * W t [] = if h = t then W t [] else 0 := by
        intro t _
        rw [K_zero]
        by_cases hht : h = t <;> simp [hht]
      rw [Finset.sum_congr rfl hid, Finset.sum_ite_eq,
        if_pos (Finset.mem_range.mpr (Nat.lt_succ_self h))]
    · -- `ℓ ≥ 1`: this is `eq:scalar-factorization` at the empty tail.
      rw [nz_singleton, if_neg (by omega)]
      exact (hF (p - 1 - h) h [] hpos).symm

/-- The frozen signature of the component-4a brief (development notes, in git history) is met
verbatim: `G_eq_W_of`
applies to the two hypotheses written out, without the abbreviations above. -/
example
    (hF : ∀ (ℓ p : ℕ) (L : List ℕ), 1 ≤ ℓ →
      W p (ℓ :: L) = ∑ t ∈ Finset.range (p + 1), K ℓ p t * W t L)
    (hK0 : ∀ ℓ p t : ℕ, p < t → K ℓ p t = 0) (p : ℕ) :
    G p = W p [] :=
  G_eq_W_of hF hK0 p

/-- **Theorem 5** (\eqref{eq:scalar-G}, first half), unconditionally: the empty-stack values
computed from the kernel table alone agree with the literal one-threshold recurrence at the
empty stack.  The two hypotheses of `G_eq_W_of` are `KernelFactor.W_factor`
(\eqref{eq:scalar-factorization}) and `KernelSupport.K_eq_zero_of_lt` (the upper half of
\cref{lem:scalar-support}). -/
theorem G_eq_W (p : ℕ) : G p = W p [] :=
  G_eq_W_of (fun _ℓ p L hℓ => W_factor hℓ p L) (fun _ _ _ h => K_eq_zero_of_lt h) p

/-! ### Theorem 6: the goal of component 4a -/

set_option linter.unusedVariables false in
/--
**Theorem 6, the goal of component 4a** (\eqref{eq:scalar-G}, `|Av_n(1342)| = G_n`, and the
correctness half of \cref{thm:scalar-algorithm}): the number computed by the scalar kernel
algorithm is the number of `1342`-avoiding permutations of `{0, …, n-1}`.

Relative to the factorization `hF` (theorem 4) and, unused, the support bound `hK0`
(theorem 1); everything else -- that `W` counts the avoiders -- is `av1342_count`, the goal
of component 3a.
-/
theorem av1342_count_kernel_of (hF : ScalarFactorization) (hK0 : KernelSupportUpper)
    (n : ℕ) : G n = (avoiders n (beta 1)).card :=
  (G_eq_W_of hF hK0 n).trans (av1342_count n)

/--
**The goal of component 4a**, unconditionally (\eqref{eq:scalar-G}, `|Av_n(1342)| = G_n`,
and the correctness half of \cref{thm:scalar-algorithm}): the number `G n` computed from the
scalar kernel table `K` by \eqref{eq:scalar-G} is the number of `1342`-avoiding permutations
of `{0, …, n-1}`.

The kernel table is the only input: `G n` is evaluated from `K` alone (`Kernel.G_eq`), the
rows `K_ℓ(p, ·)` are supported in `{0, …, p}` (`KernelSupport.K_eq_zero_of_lt`), the literal
recurrence factors through them (`KernelFactor.W_factor`), and `W` counts the avoiders
(`Counting.av1342_count`, component 3a).
-/
theorem av1342_count_kernel (n : ℕ) : G n = (avoiders n (beta 1)).card :=
  av1342_count_kernel_of (fun _ℓ p L hℓ => W_factor hℓ p L)
    (fun _ _ _ h => K_eq_zero_of_lt h) n

/-! ### \cref{ex:scalar-kernel}: from kernel rows to `|Av₄(1342)|`

The paper's worked example.  `G_four_kernel_rows` is \eqref{eq:scalar-G} at `p = 4` written
out, one group per base letter `h = 0, 1, 2, 3`; substituting the three kernel rows
`K_3(0, ·) = (5)`, `K_2(1, ·) = (4, 2)`, `K_1(2, ·) = (3, 1, 1)` -- the `h = 3` group uses
the identity kernel `K_0(3, ·) = e_3` and contributes the single term `G_3` -- gives
`G_four_grouped`, and `(G_0, G_1, G_2, G_3) = (1, 1, 2, 6)` gives `G_4 = 23`. -/

/-- \eqref{eq:scalar-G} at `p = 4`, expanded into the four groups `h = 0, 1, 2, 3`. -/
theorem G_four_kernel_rows :
    G 4 = K 3 0 0 * G 0
        + (K 2 1 0 * G 0 + K 2 1 1 * G 1)
        + (K 1 2 0 * G 0 + K 1 2 1 * G 1 + K 1 2 2 * G 2)
        + G 3 := by
  rw [G_eq 4]
  norm_num [Finset.sum_range_succ, K_zero]

set_option maxRecDepth 10000 in
/-- The kernel row `K_3(0, ·) = (5)` of \cref{ex:scalar-kernel}. -/
theorem K_row_three_zero : K 3 0 0 = 5 := by decide

set_option maxRecDepth 10000 in
/-- The kernel row `K_2(1, ·) = (4, 2)` of \cref{ex:scalar-kernel}. -/
theorem K_row_two_one : K 2 1 0 = 4 ∧ K 2 1 1 = 2 := by decide

set_option maxRecDepth 10000 in
/-- The kernel row `K_1(2, ·) = (3, 1, 1)` of \cref{ex:scalar-kernel}. -/
theorem K_row_one_two : K 1 2 0 = 3 ∧ K 1 2 1 = 1 ∧ K 1 2 2 = 1 := by decide

/-- The paper's display
`G_4 = 5G_0 + (4G_0 + 2G_1) + (3G_0 + G_1 + G_2) + G_3` (\cref{ex:scalar-kernel}). -/
theorem G_four_grouped :
    G 4 = 5 * G 0 + (4 * G 0 + 2 * G 1) + (3 * G 0 + G 1 + G 2) + G 3 := by
  rw [G_four_kernel_rows, K_row_three_zero, K_row_two_one.1, K_row_two_one.2,
    K_row_one_two.1, K_row_one_two.2.1, K_row_one_two.2.2, one_mul, one_mul]

set_option maxRecDepth 10000 in
/-- `(G_0, G_1, G_2, G_3) = (1, 1, 2, 6)` (\cref{ex:scalar-kernel}). -/
theorem G_zero_three : (G 0, G 1, G 2, G 3) = (1, 1, 2, 6) := by decide

/-- `|Av₄(1342)| = G_4 = 5 + 6 + 6 + 6 = 23` (\cref{ex:scalar-kernel}), derived from
`G_four_grouped` and `G_zero_three` rather than by evaluating `G 4`. -/
theorem G_four : G 4 = 23 := by
  have h := G_zero_three
  rw [Prod.ext_iff, Prod.ext_iff, Prod.ext_iff] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only at h0 h1 h2 h3
  rw [G_four_grouped, h0, h1, h2, h3]

end OneThreshold
end Av12453
