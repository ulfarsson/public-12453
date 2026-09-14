/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Av12453.TwoThreshold.Kernel
import Av12453.TwoThreshold.KernelSupport
import Av12453.TwoThreshold.KernelFactor
import Av12453.TwoThreshold.Counting

/-!
# Component 4b, theorems 4 and 5: the kernel algorithm counts `12453`-avoiders

This module closes the `d = 2` kernel algorithm of the sections *Protected tails and
transfer kernels* (`sec:kernels`) and *The family algorithm and its complexity*
(`sec:algorithm`) of the paper *Protected tails and polynomial-time enumeration of permutations
avoiding a direct sum of an increasing pattern and 231*:
the numbers `G 𝐩` computed from the transfer-kernel table `K` by \eqref{eq:G} agree with the
literal two-threshold recurrence `H` at the empty stack, and therefore
`G_{(n,0)} = |Av_n(12453)|`, which is \eqref{eq:answer-G} at `d = 2`.

The single input from outside is the protected-tail factorization \eqref{eq:factorization}
of \cref{cor:protected-tail},

    H 𝐩 (ℓ :: L) = ∑_{𝐭 ∈ S 𝐩} K ℓ 𝐩 𝐭 * H 𝐭 L        (ℓ ≥ 1),

which is theorem 3 of the component-4b brief (development notes, in git history)
(`H_factor`, proved in
`Av12453/TwoThreshold/KernelFactor.lean`).  It enters the proofs below only as the explicit
hypothesis `hF` of `G_eq_H_of` / `av12453_count_kernel_of`, which were written and checked
before `KernelFactor.lean` existed; `G_eq_H` and `av12453_count_kernel` discharge `hF` with
`H_factor` and are therefore unconditional.

## The proof of theorem 4

Strong induction on the control mass `‖𝐩‖₁ = p₀ + p₁`.  The two recurrences

* `Kernel.G_eq` (\eqref{eq:G} at `d = 2`) :

      G 𝐩 = 1_{𝐩 = 𝟎} + ∑_{h < p₀} G_{(h, p₁+p₀-1-h)}
                      + ∑_{h < p₁} ∑_{𝐭 ∈ S (p₀,h)} K_{δ_h}((p₀,h), 𝐭) G_𝐭,

* `Defs.H_eq_nil` (the empty-stack line of \eqref{eq:H} with \eqref{eq:initial-terminal}) :

      H 𝐩 ∅ = 1_{𝐩 = 𝟎} + ∑_{h < p₀} H_{(h, p₁+p₀-1-h)}(∅)
                        + ∑_{h < p₁} H_{(p₀,h)}(\nz(δ_h)),

have the same indicator `1_{𝐩 = 𝟎}` and the same two outer index sets `h ∈ {0, …, p₀-1}`
and `h ∈ {0, …, p₁-1}`, so it suffices to match the summands at each `h`.  Here
`T_{0,h}(𝐩) = (h, p₁+p₀-1-h)` and `U_h(𝐩) = (p₀,h)`, `δ_h = p₁-1-h`, by \eqref{eq:T} and
\eqref{eq:U}.

* **Early band.**  `‖T_{0,h}(𝐩)‖₁ = ‖𝐩‖₁ - 1 < ‖𝐩‖₁`, so the induction hypothesis applies
  termwise; this is the line of \eqref{eq:G} that carries no kernel at all.
* **Last band.**  `‖U_h(𝐩)‖₁ = p₀ + h < ‖𝐩‖₁` because `h < p₁`, and the same bound holds for
  every terminal control `𝐭 ∈ S (p₀,h)` (`mem_S`), so the induction hypothesis first
  replaces `G 𝐭` by `H 𝐭 ∅` inside the sum.  What remains at each `h` is

      ∑_{𝐭 ∈ S (p₀,h)} K_{δ_h}((p₀,h), 𝐭) H_𝐭(∅) = H_{(p₀,h)}(\nz(δ_h)),

  which splits on `δ_h`:
  * `δ_h ≥ 1`: the last-band move creates a nonempty interval, `\nz(δ_h) = (δ_h)`, and the
    identity is exactly \eqref{eq:factorization} at the empty protected tail `L = ∅`, i.e.
    `hF δ_h (p₀,h) [] hpos`.
  * `δ_h = 0` (the case `h = p₁ - 1`): no interval is created, `nz [0] = []`
    (`OneThreshold.nz_singleton`), and the identity is the paper's remark that "the identity
    kernel `K_0` handles `δ_h = 0`" in the proof of \cref{cor:empty-stack-recurrence}: the
    boundary kernel `K_0((p₀,h), ·) = 1_{(p₀,h) = ·}` collapses the sum to its single term
    `H_{(p₀,h)}(∅)` (`KernelSupport.K_zero_sum`, which is `Finset.sum_eq_single` at the
    source control, the `Finset.sum_ite_eq` step of the `d = 1` template).

Theorem 5 is then `(G_eq_H_of hF (n,0)).trans (TwoThreshold.Counting.av12453_count n)`.

The paper's unrestricted `∑_𝐭` in \eqref{eq:G} and \eqref{eq:factorization} is the finite
`∑_{𝐭 ∈ S 𝐩}` of `Kernel.G_eq` and of `hF` here; the two agree by the mass half of
\cref{lem:support} (`KernelSupport.K_eq_zero_of_mass_lt`), and
`KernelSupport.G_eq_ctrls` records \eqref{eq:G} on an arbitrary large index set.  Because
`G_eq` and `hF` are *already* stated on the same truncated index set `S (p₀,h)`, the
argument below never has to extend an index set: it uses `KernelSupport` only for
`K_zero_sum`, in the `δ_h = 0` case.

## Main results

* `TwoThresholdFactorization` : \eqref{eq:factorization} packaged as a `Prop`.
* `G_eq_H_of` : **theorem 4**, `G 𝐩 = H 𝐩 ∅`, relative to the factorization `hF`.
* `G_eq_H` : **theorem 4**, unconditionally, discharging `hF` with `KernelFactor.H_factor`.
* `av12453_count_kernel_of` : **theorem 5 and the goal of component 4b**,
  `G_{(n,0)} = |Av_n(12453)|` (\eqref{eq:answer-G} at `d = 2`), relative to `hF`, from
  `G_eq_H_of` and `Av12453.TwoThreshold.av12453_count` (the goal of component 3b).
* `av12453_count_kernel` : **theorem 5**, unconditionally -- the goal of component 4b.

## Integration (phase 3, done)

`Av12453.TwoThreshold.KernelFactor` is imported above and `hF` is discharged with
`H_factor`, in the two one-line proofs of `G_eq_H` and `av12453_count_kernel` below.  The
lambda binder is written `_ℓ` because `ℓ` is implicit in `H_factor`; naming it `ℓ` makes the
build emit a `linter.unusedVariables` warning, as component 4a's phase 3 found.  Nothing
else in this file changed at integration: `G_eq_H_aux`, `G_eq_H_of`,
`av12453_count_kernel_of`, the two frozen-signature `example`s and all the cross-checks are
as delivered.
-/

namespace Av12453
namespace TwoThreshold

open OneThreshold (nz nz_singleton avoiders)

/-! ### The hypothesis

`TwoThresholdFactorization` is \eqref{eq:factorization} of \cref{cor:protected-tail} at
`d = 2`; it is theorem 3 of the brief, proved in the sibling module `KernelFactor.lean`.
Stating it as a hypothesis keeps this module independent of that proof. -/

/-- **\eqref{eq:factorization}** as a hypothesis: the protected-tail factorization of the
literal two-threshold recurrence `H` through the transfer kernel `K`.  Discharged by
`KernelFactor.H_factor`. -/
def TwoThresholdFactorization : Prop :=
  ∀ (ℓ : ℕ) (p : ℕ × ℕ) (L : List ℕ), 1 ≤ ℓ →
    H p (ℓ :: L) = ∑ t ∈ S p, K ℓ p t * H t L

/-! ### Theorem 4: the kernel values are the empty-stack values -/

/-- The induction behind `G_eq_H_of`, on the control mass `‖𝐩‖₁ = p₀ + p₁`, which
`sec:algorithm` verifies is a topological order for \eqref{eq:G}. -/
private theorem G_eq_H_aux (hF : TwoThresholdFactorization) :
    ∀ N (p : ℕ × ℕ), p.1 + p.2 ≤ N → G p = H p [] := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro p hN
    -- The two recurrences have the same indicator and the same two outer index sets.
    rw [G_eq p, H_eq_nil p]
    /- Early band `T_{0,h}(𝐩) = (h, p₁+p₀-1-h)`: mass `‖𝐩‖₁ - 1`, so the induction
    hypothesis applies directly.  No kernel occurs in this group. -/
    have hearly : (∑ h ∈ Finset.range p.1, G (h, p.2 + p.1 - 1 - h))
        = ∑ h ∈ Finset.range p.1, H (h, p.2 + p.1 - 1 - h) [] := by
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [Finset.mem_range] at hh
      exact ih (N - 1) (by omega) (h, p.2 + p.1 - 1 - h) (by simp; omega)
    /- Last band `U_h(𝐩) = (p₀, h)` with `δ_h = p₁ - 1 - h`: mass `p₀ + h < ‖𝐩‖₁`. -/
    have hlast : (∑ h ∈ Finset.range p.2,
          ∑ t ∈ S (p.1, h), K (p.2 - 1 - h) (p.1, h) t * G t)
        = ∑ h ∈ Finset.range p.2, H (p.1, h) (nz [p.2 - 1 - h]) := by
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [Finset.mem_range] at hh
      -- Induction hypothesis: `G 𝐭 = H 𝐭 ∅` for every `𝐭 ∈ S (p₀, h)`, since
      -- `‖𝐭‖₁ ≤ p₀ + h < ‖𝐩‖₁`.
      have hG : ∀ t ∈ S (p.1, h),
          K (p.2 - 1 - h) (p.1, h) t * G t = K (p.2 - 1 - h) (p.1, h) t * H t [] := by
        intro t ht
        rw [mem_S] at ht
        simp only at ht
        rw [ih (N - 1) (by omega) t (by omega)]
      rw [Finset.sum_congr rfl hG]
      rcases Nat.eq_zero_or_pos (p.2 - 1 - h) with hz | hpos
      · -- `δ_h = 0` (the case `h = p₁ - 1`): no interval is created, `nz [0] = []`, and the
        -- boundary kernel `K_0` collapses the sum to its `𝐭 = (p₀, h)` term.
        rw [hz, nz_singleton, if_pos rfl]
        exact K_zero_sum (p.1, h) fun t => H t []
      · -- `δ_h ≥ 1`: this is `eq:factorization` at the empty protected tail.
        rw [nz_singleton, if_neg (by omega)]
        exact (hF (p.2 - 1 - h) (p.1, h) [] hpos).symm
    rw [hearly, hlast]

/--
**Theorem 4** (the first half of \eqref{eq:answer-G}): the empty-stack values `G_𝐩` computed
from the transfer-kernel table alone by \eqref{eq:G} agree with the literal two-threshold
recurrence \eqref{eq:H} at the empty stack, `G_𝐩 = H_𝐩(∅)`.

Relative to the factorization `hF` (\eqref{eq:factorization} of \cref{cor:protected-tail},
theorem 3 of the brief, `KernelFactor.H_factor`).
-/
theorem G_eq_H_of (hF : TwoThresholdFactorization) (p : ℕ × ℕ) : G p = H p [] :=
  G_eq_H_aux hF (p.1 + p.2) p le_rfl

/-- The frozen signature of the component-4b brief (development notes, in git history) is
met verbatim: `G_eq_H_of`
applies to the hypothesis written out, without the abbreviation above. -/
example
    (hF : ∀ (ℓ : ℕ) (p : ℕ × ℕ) (L : List ℕ), 1 ≤ ℓ →
      H p (ℓ :: L) = ∑ t ∈ S p, K ℓ p t * H t L) (p : ℕ × ℕ) :
    G p = H p [] :=
  G_eq_H_of hF p

/--
**Theorem 4**, unconditionally: `G_𝐩 = H_𝐩(∅)`.  The hypothesis `hF` of `G_eq_H_of` is
\eqref{eq:factorization}, discharged with `KernelFactor.H_factor`.
-/
theorem G_eq_H (p : ℕ × ℕ) : G p = H p [] :=
  G_eq_H_of (fun _ℓ p L hℓ => H_factor hℓ p L) p

/-! ### Theorem 5: the goal of component 4b -/

/--
**Theorem 5, the goal of component 4b** (\eqref{eq:answer-G} at `d = 2`,
`a_n^{(2)} = G_{(n,0)}`): the number computed by the two-threshold kernel algorithm is the
number of `12453`-avoiding permutations of `{0, …, n-1}`.  This is the correctness half of
the paper's polynomial-time algorithm for `12453`.

Relative to the factorization `hF` (theorem 3); everything else -- that the literal
recurrence `H` counts the avoiders -- is `Av12453.TwoThreshold.av12453_count`, the goal of
component 3b.
-/
theorem av12453_count_kernel_of (hF : TwoThresholdFactorization) (n : ℕ) :
    G (n, 0) = (avoiders n (beta 2)).card :=
  (G_eq_H_of hF (n, 0)).trans (av12453_count n)

/-- The frozen signature of theorem 5 is met verbatim. -/
example
    (hF : ∀ (ℓ : ℕ) (p : ℕ × ℕ) (L : List ℕ), 1 ≤ ℓ →
      H p (ℓ :: L) = ∑ t ∈ S p, K ℓ p t * H t L) (n : ℕ) :
    G (n, 0) = (avoiders n (beta 2)).card :=
  av12453_count_kernel_of hF n

/--
**Theorem 5 and the goal of component 4b**, unconditionally: \eqref{eq:answer-G} at
`d = 2`, `a_n^{(2)} = G_{(n,0)}`.  The number computed by the two-threshold kernel algorithm
of \eqref{eq:K}--\eqref{eq:G} is the number of `12453`-avoiding permutations of
`{0, …, n-1}`.  The hypothesis `hF` of `av12453_count_kernel_of` is
\eqref{eq:factorization}, discharged with `KernelFactor.H_factor`.
-/
theorem av12453_count_kernel (n : ℕ) : G (n, 0) = (avoiders n (beta 2)).card :=
  av12453_count_kernel_of (fun _ℓ p L hℓ => H_factor hℓ p L) n

/-! ### Cross-checks

`G_eq_H_of` and `av12453_count_kernel_of` are conditional on `hF`, so they cannot be
instantiated numerically until phase 2a lands.  Their *conclusions*, however, are closed
computable statements, and both are checked here against the two independent
implementations already in the development: the kernel table `K`/`G` of `Kernel.lean` and
the literal recurrence `H` of `Defs.lean` (which `Counting.av12453_count` proves counts the
avoiders, and which `Counting.lean` itself cross-checks against a brute-force enumeration of
`Av_k(12453)` through `k = 7`).

The `decide`s are kernel evaluations and add no axiom; the `#eval`s are guarded by
`#guard_msgs`, so the build fails if any value ever changes.  Note that
`(avoiders k (beta 2)).card` cannot be `decide`d: `perms` goes through `List.permutations`,
which the kernel does not reduce. -/

set_option maxRecDepth 1000000 in
/-- **Theorem 4 checked numerically** for `‖𝐩‖₁ ≤ 6` at the initial controls `(k, 0)` of
\eqref{eq:initial-terminal}: the value computed from the kernel table by \eqref{eq:G} and
the value of the literal recurrence \eqref{eq:H} at the empty stack agree. -/
example : ∀ k ∈ [0, 1, 2, 3, 4, 5, 6], G (k, 0) = H (k, 0) [] := by decide

set_option maxRecDepth 1000000 in
/-- **Theorem 4 checked numerically** at controls with both coordinates positive, where the
early-band group of \eqref{eq:G} is nonempty. -/
example : ∀ p ∈ [((1 : ℕ), (2 : ℕ)), (2, 1), (2, 2), (1, 3), (3, 1)], G p = H p [] := by
  decide

/-! **Theorem 5 checked numerically** for `n ≤ 7`: the kernel algorithm's output
`G_{(n,0)}`, and its agreement with a brute-force enumeration of `Av_n(12453)`.  The first
`#eval` prints the first eight terms of \eqref{eq:first-terms}; the second compares them,
term by term, with `(avoiders k (beta 2)).card`.  (The comparison is printed as a list of
booleans rather than as a list of pairs so that the enumeration is run only once: filtering
`7! = 5040` words by `Contains _ (beta 2)` is by far the most expensive line of this
file.) -/

set_option linter.hashCommand false in
/-- info: [1, 1, 2, 6, 24, 119, 694, 4581] -/
#guard_msgs in
#eval (List.range 8).map (fun k => G (k, 0))

set_option linter.hashCommand false in
/-- info: [true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval (List.range 8).map (fun k => G (k, 0) == (avoiders k (beta 2)).card)

/-! The same comparison against the literal recurrence `H`, to `n = 9`: the ten terms
`1, 1, 2, 6, 24, 119, 694, 4581, 33286, 260927` of \eqref{eq:first-terms}, computed once
from the kernel table by \eqref{eq:G} and once from \eqref{eq:H}.  This is the numerical
content of theorem 4 beyond the `decide` range above. -/

set_option linter.hashCommand false in
/-- info: [true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval (List.range 10).map (fun k => G (k, 0) == H (k, 0) [])

/-! ### The frozen interface of the component-4b brief (development notes, in git history)

Phase 1 of component 4b froze the statements of theorems 1--5 as `sorry` placeholders in a
scratch module `TwoThreshold/KernelInterface.lean`, which phase 3 deleted.  The five
`example`s below are those five statements, transcribed verbatim from that file and
discharged by the delivered theorems, so that the frozen interface is checked at compile
time and any later drift in a binder, an implicit argument or an index set is caught here.
-/

/-- Theorem 1 (`KernelSupport`). -/
example {ℓ : ℕ} {p t : ℕ × ℕ} (h : p.1 + p.2 < t.1 + t.2) : K ℓ p t = 0 :=
  K_eq_zero_of_mass_lt h

/-- Theorem 2 (`KernelSupport`), \eqref{eq:support}. -/
example {ℓ : ℕ} {p t : ℕ × ℕ} (hℓ : 1 ≤ ℓ) (h : K ℓ p t ≠ 0) :
    t = p ∨ t.1 + t.2 + 1 ≤ p.1 + p.2 :=
  K_support hℓ h

/-- Theorem 3 (`KernelFactor`), \eqref{eq:factorization}. -/
example {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (p : ℕ × ℕ) (L : List ℕ) :
    H p (ℓ :: L) = ∑ t ∈ S p, K ℓ p t * H t L :=
  H_factor hℓ p L

/-- Theorem 4, `G_𝐩 = H_𝐩(∅)`. -/
example (p : ℕ × ℕ) : G p = H p [] := G_eq_H p

/-- Theorem 5, the goal of component 4b, \eqref{eq:answer-G} at `d = 2`. -/
example (n : ℕ) : G (n, 0) = (avoiders n (beta 2)).card := av12453_count_kernel n

end TwoThreshold
end Av12453
