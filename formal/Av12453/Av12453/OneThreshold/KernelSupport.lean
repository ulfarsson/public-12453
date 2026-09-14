/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Av12453.OneThreshold.Kernel

/-!
# Exact support of the scalar kernel rows

This file proves \cref{lem:scalar-support} (*Exact scalar support*) of the subsection
*The scalar kernel algorithm* of Section 2 of the paper
*Protected tails and polynomial-time enumeration of permutations avoiding a direct sum of an
increasing pattern and 231*, for `d = 1`: for every source
control `p` and every active-head size `ℓ ≥ 1`,
`supp K_ℓ(p, ·) = {0, 1, …, p}`, and `K_ℓ(p, p) = C_ℓ` is the `ℓ`-th Catalan number.

The kernel `K` itself, its defining equations `K_zero`, `K_succ_eq`, `D_eq` and the
empty-stack values `G` are `Av12453.OneThreshold.Kernel`; nothing here uses the literal
recurrence `W`.

## The three statements

* `K_eq_zero_of_lt` (upper half of \eqref{eq:scalar-support}) : `p < t → K ℓ p t = 0`.
  The paper's reason is that a base move strictly decreases the control and an
  active-interval move leaves it unchanged, so no path from control `p` reaches a terminal
  control above `p`.  Formally this is a strong induction on the *grade* `p + ℓ`, the
  topological order of the kernel dependencies used in `Kernel.lean`: the base terms of
  \eqref{eq:scalar-K} have grade `p + ℓ - 1` and source control `h < p < t`, the endpoint
  term `D` has grade `p + ℓ - 1` and the same controls, and in a split term
  `K_a(p, u) K_b(u, t)` the right factor has grade `u + b ≤ p + ℓ - 2` and source control
  `u ≤ p < t`.
* `K_diag_eq_catalan` (the diagonal) : `K ℓ p p = C_ℓ`.  By `K_eq_zero_of_lt` every base
  term vanishes at `t = p` (its source control is `h < p`) and every split term keeps only
  its `u = p` summand, so the recurrence collapses to
  `K_ℓ(p, p) = 2 C_{ℓ-1} + ∑_{a=1}^{ℓ-2} C_a C_{ℓ-1-a}`, which is Segner's recurrence
  `catalan_succ` with its two extreme summands `a = 0` and `a = ℓ - 1` separated
  (`catalan_split`).
* `K_pos` (lower half of \eqref{eq:scalar-support}) : `1 ≤ ℓ → t ≤ p → 0 < K ℓ p t`.  For
  `t = p` this is `K_diag_eq_catalan` and `catalan_pos`.  For `t < p` the paper takes the
  base move with `h = t` -- the unique base letter having exactly `t` unread base letters
  below it -- and then exhausts the resulting active interval of size `ℓ + p - 1 - t` by
  endpoints; here that is the observation that the base term `K_{ℓ+p-1-t}(t, t) = C_{ℓ+p-1-t}`
  is one positive summand of a sum of naturals.

## Main results

* `K_eq_zero_of_lt`, `K_pos`, `K_diag_eq_catalan` : \cref{lem:scalar-support}.
* `K_support_eq` : the two halves combined, `supp K_ℓ(p, ·) = {0, …, p}` for `ℓ ≥ 1`, as an
  `↔` on the value of `K`.
* `K_sum_extend`, `K_sum_extend_left` : consequences used downstream -- a sum of
  `K ℓ p t` over `t` may be taken over any range containing `{0, …, p}`.
* `K_succ_eq_range`, `G_eq_range` : \eqref{eq:scalar-K} and \eqref{eq:scalar-G} with the
  paper's own (unrestricted) summation ranges, added at integration.
-/

namespace Av12453
namespace OneThreshold

/-! ### Two facts about Catalan numbers

Mathlib's `catalan_succ` is Segner's recurrence `C_{m+1} = ∑_{i=0}^{m} C_i C_{m-i}` over
`Fin (m+1)`.  The kernel recurrence \eqref{eq:scalar-K} produces the same sum with its two
extreme summands `i = 0` and `i = m` already separated (they are the two endpoint choices of
\eqref{eq:scalar-D}), so `catalan_split` is the form we need.  `catalan_pos` is not in
Mathlib; it follows from `succ_mul_catalan_eq_centralBinom`. -/

/-- Segner's recurrence over `Finset.range`, rather than over `Fin`. -/
private theorem catalan_succ_range (m : ℕ) :
    catalan (m + 1) = ∑ k ∈ Finset.range (m + 1), catalan k * catalan (m - k) := by
  rw [catalan_succ']
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => catalan x * catalan y) m

/-- **Segner's recurrence with its two extreme summands separated.**  For `m ≥ 1`,
`C_{m+1} = 2 C_m + ∑_{a=1}^{m-1} C_a C_{m-a}`: the summands `a = 0` and `a = m` of
`catalan_succ` both contribute `C_0 C_m = C_m`.  This is exactly the shape in which
\eqref{eq:scalar-K} produces `K_{m+1}(p, p)`, the two extreme summands being the two
endpoint choices of \eqref{eq:scalar-D}. -/
private theorem catalan_split {m : ℕ} (hm : 1 ≤ m) :
    catalan (m + 1) = 2 * catalan m + ∑ a ∈ Finset.Ico 1 m, catalan a * catalan (m - a) := by
  rw [catalan_succ_range, Finset.sum_range_succ, Nat.sub_self, catalan_zero, Nat.mul_one,
    Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hm]
  simp only [Nat.zero_add, Nat.sub_zero, catalan_zero, Nat.one_mul]
  omega

/-- Every Catalan number is positive.  (Mathlib has no `catalan_pos`; the proof is
`(m + 1) C_m = \binom{2m}{m} > 0`.) -/
private theorem catalan_pos (m : ℕ) : 0 < catalan m := by
  rcases Nat.eq_zero_or_pos (catalan m) with h | h
  · exact absurd (by rw [← succ_mul_catalan_eq_centralBinom m, h, Nat.mul_zero] :
      Nat.centralBinom m = 0) (Nat.centralBinom_pos m).ne'
  · exact h

/-! ### Theorem 1: the rows vanish above the source control -/

/-- The induction behind `K_eq_zero_of_lt`, on the grade `p + ℓ`. -/
private theorem K_eq_zero_of_lt_aux : ∀ N ℓ p t, p + ℓ ≤ N → p < t → K ℓ p t = 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro ℓ p t hN hpt
    match ℓ with
    | 0 => rw [K_zero, if_neg (by omega)]
    | j + 1 =>
      rw [K_succ_eq (Nat.le_add_left 1 j) p t]
      have hbase : (∑ h ∈ Finset.range p, K (j + 1 + p - 1 - h) h t) = 0 := by
        refine Finset.sum_eq_zero fun h hh => ?_
        rw [Finset.mem_range] at hh
        exact ih (N - 1) (by omega) (j + 1 + p - 1 - h) h t (by omega) (by omega)
      have hD : D (j + 1) p t = 0 := by
        rw [D_eq]
        split_ifs with h1 h2
        · omega
        · rfl
        · rw [ih (N - 1) (by omega) (j + 1 - 1) p t (by omega) hpt, Nat.mul_zero]
      have hsplit : (∑ a ∈ Finset.Ico 1 (j + 1 - 1),
          ∑ u ∈ Finset.range (p + 1), K a p u * K (j + 1 - 1 - a) u t) = 0 := by
        refine Finset.sum_eq_zero fun a ha => ?_
        rw [Finset.mem_Ico] at ha
        refine Finset.sum_eq_zero fun u hu => ?_
        rw [Finset.mem_range] at hu
        rw [ih (N - 1) (by omega) (j + 1 - 1 - a) u t (by omega) (by omega), Nat.mul_zero]
      rw [hbase, hD, hsplit]

/-- **\cref{lem:scalar-support}, upper half**: a scalar kernel row `K_ℓ(p, ·)` vanishes
above its source control, because a base move strictly decreases the control and an
active-interval move leaves it unchanged.  Hence `supp K_ℓ(p, ·) ⊆ {0, …, p}`, which is what
makes the restricted ranges of `Kernel.K_succ_eq` and `Kernel.G_eq` agree with the paper's
unrestricted sums. -/
theorem K_eq_zero_of_lt {ℓ p t : ℕ} (h : p < t) : K ℓ p t = 0 :=
  K_eq_zero_of_lt_aux (p + ℓ) ℓ p t le_rfl h

/-! ### Theorem 3: the diagonal is a Catalan number -/

/-- **\cref{lem:scalar-support}, the diagonal**: `K_ℓ(p, p) = C_ℓ`.  A stopped path ending
at control `p` uses no base move, so it is one of the `C_ℓ` orders in which the active
interval of size `ℓ` can be consumed (`lem:first-letter`).  Formally: by
`K_eq_zero_of_lt` the base terms of \eqref{eq:scalar-K} vanish at `t = p` and each split
term keeps only its `u = p` summand, so the recurrence becomes Segner's recurrence
(`catalan_split`). -/
theorem K_diag_eq_catalan (ℓ p : ℕ) : K ℓ p p = catalan ℓ := by
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    /- The base terms `K_{ℓ+p-1-h}(h, p)` all vanish: their source control is `h < p`. -/
    have hbase : ∀ ℓ' : ℕ, (∑ h ∈ Finset.range p, K (ℓ' + p - 1 - h) h p) = 0 := by
      intro ℓ'
      refine Finset.sum_eq_zero fun h hh => ?_
      exact K_eq_zero_of_lt (Finset.mem_range.mp hh)
    match ℓ, ih with
    | 0, _ => rw [K_zero, if_pos rfl, catalan_zero]
    | 1, _ =>
      rw [K_succ_eq le_rfl p p, hbase 1, D_one, if_pos rfl, catalan_one]
      simp
    | j + 2, ih =>
      have hjp : 1 ≤ j + 1 := Nat.le_add_left 1 j
      /- Each split term collapses to its `u = p` summand, again by `K_eq_zero_of_lt`. -/
      have hsplit : ∀ a ∈ Finset.Ico 1 (j + 2 - 1),
          (∑ u ∈ Finset.range (p + 1), K a p u * K (j + 2 - 1 - a) u p) =
            catalan a * catalan (j + 1 - a) := by
        intro a ha
        rw [Finset.mem_Ico] at ha
        rw [Finset.sum_eq_single p
          (fun u hu hup => by
            rw [K_eq_zero_of_lt (Nat.lt_of_le_of_ne (by
              have := Finset.mem_range.mp hu; omega) hup), Nat.mul_zero])
          (fun hp => absurd (Finset.mem_range.mpr (Nat.lt_succ_self p)) hp),
          ih a (by omega), ih (j + 2 - 1 - a) (by omega)]
        congr 2
      rw [K_succ_eq (by omega) p p, hbase (j + 2), D_succ (by omega) p p,
        Finset.sum_congr rfl hsplit, Nat.zero_add,
        show j + 2 - 1 = j + 1 from rfl, ih (j + 1) (by omega),
        catalan_split hjp]

/-! ### Theorem 2: every terminal control at most the source control occurs -/

/-- **\cref{lem:scalar-support}, lower half**: for `ℓ ≥ 1` every terminal control
`t ∈ {0, …, p}` is actually attained, so together with `K_eq_zero_of_lt` the support of
`K_ℓ(p, ·)` is exactly `{0, …, p}`.  For `t = p` this is `K_diag_eq_catalan`; for `t < p`
the paper's witness is the base move with `h = t`, followed by endpoint moves only, and the
weight of that family of paths is the single base summand
`K_{ℓ+p-1-t}(t, t) = C_{ℓ+p-1-t} > 0`. -/
theorem K_pos {ℓ p t : ℕ} (hℓ : 1 ≤ ℓ) (ht : t ≤ p) : 0 < K ℓ p t := by
  rcases eq_or_lt_of_le ht with rfl | hlt
  · rw [K_diag_eq_catalan]
    exact catalan_pos ℓ
  · obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
    rw [K_succ_eq (Nat.le_add_left 1 j) p t]
    have hle : K (j + 1 + p - 1 - t) t t ≤ ∑ h ∈ Finset.range p, K (j + 1 + p - 1 - h) h t :=
      Finset.single_le_sum (f := fun h => K (j + 1 + p - 1 - h) h t)
        (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr hlt)
    have hpos : 0 < K (j + 1 + p - 1 - t) t t := by
      rw [K_diag_eq_catalan]
      exact catalan_pos _
    omega

/-! ### The support statement, and range extension

`K_support_eq` is \eqref{eq:scalar-support} itself.  `K_sum_extend` records the consequence
advertised in the brief: because the rows vanish above `p`, a sum of `K ℓ p t` over `t` may
be taken over `Finset.range (p + 1)` or over any larger range, so the restricted ranges used
in `Kernel.K_succ_eq` and `Kernel.G_eq` really do reproduce the paper's `∑_{t ≥ 0}`. -/

/-- **\eqref{eq:scalar-support}**: `supp K_ℓ(p, ·) = {0, 1, …, p}` for `ℓ ≥ 1`. -/
theorem K_support_eq {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (p t : ℕ) : K ℓ p t ≠ 0 ↔ t ≤ p := by
  constructor
  · intro h
    by_contra hc
    exact h (K_eq_zero_of_lt (by omega))
  · intro h
    exact (K_pos hℓ h).ne'

/-- A sum of `f t * K ℓ p t` over `t` may be extended from `{0, …, p}` to any larger
range: the omitted terms vanish by `K_eq_zero_of_lt`. -/
theorem K_sum_extend {p N : ℕ} (hN : p + 1 ≤ N) (ℓ : ℕ) (f : ℕ → ℕ) :
    (∑ t ∈ Finset.range (p + 1), K ℓ p t * f t) = ∑ t ∈ Finset.range N, K ℓ p t * f t := by
  refine Finset.sum_subset (Finset.range_subset_range.mpr hN) fun t _ ht => ?_
  simp only [Finset.mem_range, not_lt] at ht
  rw [K_eq_zero_of_lt (show p < t by omega), Nat.zero_mul]

/-- The same extension with the kernel on the right of the product, as it occurs in the
split terms of \eqref{eq:scalar-K}. -/
theorem K_sum_extend_left {p N : ℕ} (hN : p + 1 ≤ N) (ℓ : ℕ) (f : ℕ → ℕ) :
    (∑ t ∈ Finset.range (p + 1), f t * K ℓ p t) = ∑ t ∈ Finset.range N, f t * K ℓ p t := by
  refine Finset.sum_subset (Finset.range_subset_range.mpr hN) fun t _ ht => ?_
  simp only [Finset.mem_range, not_lt] at ht
  rw [K_eq_zero_of_lt (show p < t by omega), Nat.mul_zero]

/-! ### The paper's unrestricted sums  (added at integration, phase 3)

\eqref{eq:scalar-K} sums the split term over *all* `u ≥ 0` and \eqref{eq:scalar-G} sums `t`
over *all* `t ≥ 0`, whereas `Kernel.K_succ_eq` and `Kernel.G_eq` use the truncated ranges
`{0, …, p}` and `{0, …, h}` — the truncation being what makes the recursion terminate on the
grade before a support lemma is available.  The two lemmas below record that the truncation
is exactly the support restriction of `K_eq_zero_of_lt`: the same equations hold with the
inner sum taken over `Finset.range N` for *any* `N` large enough to contain the support, so
nothing is lost.  (`Finset.range N` with `N` arbitrary is the finitary reading of the
paper's `∑_{u ≥ 0}`: all but finitely many summands vanish.) -/

/-- **\eqref{eq:scalar-K} with the paper's summation range**: the split term of the kernel
recurrence may be summed over any `Finset.range N` with `N ≥ p + 1`, because
`K_a(p, u) = 0` for `u > p`. -/
theorem K_succ_eq_range {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (p t : ℕ) {N : ℕ} (hN : p + 1 ≤ N) :
    K ℓ p t =
      (∑ h ∈ Finset.range p, K (ℓ + p - 1 - h) h t)
        + D ℓ p t
        + ∑ a ∈ Finset.Ico 1 (ℓ - 1),
            ∑ u ∈ Finset.range N, K a p u * K (ℓ - 1 - a) u t := by
  rw [K_succ_eq hℓ p t]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  exact K_sum_extend hN a (fun u => K (ℓ - 1 - a) u t)

/-- **\eqref{eq:scalar-G} with the paper's summation range**: the inner sum over terminal
controls may be taken over any `Finset.range N` with `N ≥ p`, because the row
`K_{p-1-h}(h, ·)` vanishes above `h < p`. -/
theorem G_eq_range (p : ℕ) {N : ℕ} (hN : p ≤ N) :
    G p = (if p = 0 then 1 else 0)
      + ∑ h ∈ Finset.range p, ∑ t ∈ Finset.range N, K (p - 1 - h) h t * G t := by
  rw [G_eq p]
  congr 1
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.mem_range] at hh
  exact K_sum_extend (by omega) (p - 1 - h) G

/-! ### Cross-checks against `ex:scalar-kernel`

The paper's example rows are `K_3(0, ·) = (5)`, `K_2(1, ·) = (4, 2)` and
`K_1(2, ·) = (3, 1, 1)`, so their diagonal entries are `K_3(0,0) = 5 = C_3`,
`K_2(1,1) = 2 = C_2` and `K_1(2,2) = 1 = C_1`.  Each is checked twice below: once through
`K_diag_eq_catalan` and Mathlib's `catalan`, and once by evaluating the recurrence
\eqref{eq:scalar-K} in the kernel (`decide`).  Both routes add no axioms. -/

example : K 3 0 0 = 5 := by rw [K_diag_eq_catalan, catalan_three]

set_option maxRecDepth 10000 in
example : K 3 0 0 = 5 := by decide

example : K 2 1 1 = 2 := by rw [K_diag_eq_catalan, catalan_two]

set_option maxRecDepth 10000 in
example : K 2 1 1 = 2 := by decide

example : K 1 2 2 = 1 := by rw [K_diag_eq_catalan, catalan_one]

set_option maxRecDepth 10000 in
example : K 1 2 2 = 1 := by decide

/-- The off-diagonal entries of the same rows are positive (`K_pos`) and vanish above the
source control (`K_eq_zero_of_lt`); `decide` confirms `K_1(2, ·) = (3, 1, 1)` and
`K_1(2, 3) = 0`. -/
example : 0 < K 1 2 0 ∧ 0 < K 1 2 1 ∧ 0 < K 1 2 2 :=
  ⟨K_pos le_rfl (by omega), K_pos le_rfl (by omega), K_pos le_rfl le_rfl⟩

example : K 1 2 3 = 0 := K_eq_zero_of_lt (by omega)

end OneThreshold
end Av12453
