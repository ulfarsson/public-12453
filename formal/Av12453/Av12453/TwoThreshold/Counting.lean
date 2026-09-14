/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Av12453.TwoThreshold.Semantics

/-!
# Component 3b, theorem (D): the two-threshold recurrence counts the completions

This module proves the counting half of the two-threshold construction: for every legal
prefix `σ`, the number `A n σ` of `12453`-avoiding permutations of `{0, …, n-1}` beginning
with `σ` equals `H (p n σ) (L n σ)`, the paper's `H_{\mathbf p}(L)` at `d = 2` evaluated at
the abstract state of `σ`.  Specializing to `σ = []`, where the state is the initial state
`(𝐩, L) = ((n, 0), ∅)` of \eqref{eq:initial-terminal}, gives

    H (n, 0) [] = |Av_n(12453)|,

the goal of component 3b.

The proof is the induction of \cref{thm:literal} at `d = 2`, run on the measure
`ρ(𝐩, L) = p₀ + p₁ + |L|` of \eqref{eq:rho}, which by `rho_eq` is the number of unread
values and by `card_unread_succ` drops by one at every move.  The prefix partition `A_succ`
writes `A n σ` as a sum over the unread values, and `sum_unread_split` together with the
layout invariant regroups that sum exactly as the four lines of \eqref{eq:H}:

* the **early-band letters** `x ∈ B₀`, reindexed by the number `h = below0 n σ x` of
  band-`0` values below them, `h = 0, …, p₀-1` (`sum_below0_eq`); each contributes
  `H (h, p₁ + p₀ - 1 - h) L`, i.e. `H_{T_{0,h}(𝐩)}(L)` by \eqref{eq:T}.  This group is the
  one with no `d = 1` analogue;
* the **last-band letters** `x ∈ B₁`, reindexed by `h = below1 n σ x`, `h = 0, …, p₁-1`
  (`sum_below1_eq`); each contributes `H (p₀, h) (nz ((ℓ₁ + δ_h) :: L'))` with
  `δ_h = p₁ - 1 - h`, i.e. `H_{U_h(𝐩)}(\nz(ℓ₁+δ_h, ℓ₂, …))` by \eqref{eq:U} and
  \cref{lem:merger}.  At an empty stack `ℓ₁ = 0` and `\nz` deletes an empty merger set;
* the **active-head letters** `x ∈ I₁`, reindexed by their local rank
  `r = 0, …, ℓ₁-1` (`sum_rank_eq`); the two endpoints `r = 0` and `r = ℓ₁-1` give the
  endpoint term `Eend ℓ₁ 𝐩 L'` of line 3 (two letters when `ℓ₁ ≥ 2`, one when `ℓ₁ = 1`),
  and each interior rank gives one term of line 4 (`sum_rank_split`);
* the **deferred letters**, in an interval `I_j` with `j ≥ 2`, which contribute `0` by
  theorem (B).

Theorems (B) and (C) of the component enter only through the hypotheses
`Av12453.TwoThreshold.DeferredHyp` and `Av12453.TwoThreshold.CompleteHyp` of `Defs.lean`;
`A_eq_H_of` and `av12453_count_of` are stated relative to them, so that they are
axiom-clean and independent of how (B) and (C) are proved.  The unconditional `A_eq_H` and
`av12453_count` discharge the two hypotheses with the theorems of the same name proved in
`Av12453.TwoThreshold.Semantics`.

## Main results

* `sum_rank_split` : the local-rank sum over the active head is the endpoint term plus the
  interior terms, i.e. the last two lines of \eqref{eq:H}.
* `A_eq_H_of` : **(D)**, relative to (B) and (C).
* `av12453_count_of` : **the goal of component 3b**, relative to (B) and (C).
* `H_pos` : `H` is positive at every composition with positive parts -- the maximal
  recurrence path of \cref{prop:scan-states}(c)'s proof.
* `exists_completion_of_legal_of`, `legal_of_prefix_avoider_of`,
  `legal_iff_prefix_avoider_of` : legality is exactly "initial segment of a `12453`-avoiding
  permutation", the `d = 2` analogue of the phase-3 addition of component 3a.
* **`A_eq_H`**, **`av12453_count`** : the same two theorems unconditionally, with (B) and
  (C) discharged from `Av12453.TwoThreshold.Semantics`.  `av12453_count` is the goal of
  component 3b.
* **`legal_iff_prefix_avoider`** (with `exists_completion_of_legal` and
  `legal_of_prefix_avoider`) : the same, unconditionally.

The two unconditional forms `A_eq_H` and `av12453_count` of the frozen interface are the
`_of` forms with (B) and (C) discharged; they are proved in the "Discharging (B) and (C)"
section at the end of this file.

## Numerical check

Both sides of `av12453_count` are computable, and evaluating them independently returns the
first terms `1, 1, 2, 6, 24, 119, 694, 4581` of `|Av_n(12453)|`
(`code/data/av12453_terms_0_300.txt`, the paper's \eqref{eq:first-terms}); see the
`#guard_msgs`-guarded `#eval` at the end of this file.  The check is not a `decide`: `perms`
goes through `List.permutations`, which the kernel does not reduce.
-/

namespace Av12453
namespace TwoThreshold

open OneThreshold (unread mem_unread IsWord card_unread nz nz_singleton stackUnion
  mem_stackUnion perms mem_perms avoiders sum_rank_eq)

variable {n : ℕ} {σ : List ℕ} {x : ℕ}

/-! ### Deleting zeros from a two-entry list

The four shapes of `\nz(r, ℓ - 1 - r)` that an active-interval move produces. -/

theorem nz_two {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : nz [a, b] = [a, b] := by
  simp [OneThreshold.nz, ha, hb]

theorem nz_two_left_zero {b : ℕ} (hb : b ≠ 0) : nz [0, b] = [b] := by
  simp [OneThreshold.nz, hb]

theorem nz_two_right_zero {a : ℕ} (ha : a ≠ 0) : nz [a, 0] = [a] := by
  simp [OneThreshold.nz, ha]

theorem nz_two_zero_zero : nz [(0 : ℕ), 0] = [] := by
  simp [OneThreshold.nz]

/-! ### The active head: local ranks give the endpoint and interior terms

`sum_rank_split` is the arithmetic heart of the regrouping, and is line 3 plus line 4 of
\eqref{eq:H}.  Reading the value of local rank `r` of an active head of size `ℓ` leaves the
two pieces of sizes `r` and `ℓ - 1 - r`, with empty pieces deleted (`pL_succ_active`).  The
extreme ranks `r = 0` and `r = ℓ - 1` both leave the single piece of size `ℓ - 1` -- these
are the paper's two endpoints, counted with multiplicity two in `min(2, ℓ₁)`, and they
coincide only when `ℓ = 1`, where there is one endpoint and no piece at all.  The remaining
ranks `r = 1, …, ℓ - 2` leave two nonempty pieces `(a, b)` with `a + b = ℓ - 1`, which under
`a = j - 1` are the interior terms `j = 2, …, ℓ₁ - 1` of line 4. -/

theorem sum_rank_split (q : ℕ × ℕ) (T : List ℕ) :
    ∀ ℓ : ℕ, 1 ≤ ℓ →
      ∑ r ∈ Finset.range ℓ, H q (nz [r, ℓ - 1 - r] ++ T)
        = Eend ℓ q T + ∑ a ∈ Finset.Ico 1 (ℓ - 1), H q (a :: (ℓ - 1 - a) :: T) := by
  intro ℓ hℓ
  obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · -- `ℓ = 1`: one endpoint, no interior ranks.
    rw [Finset.sum_range_one, Nat.zero_sub, nz_two_zero_zero, List.nil_append,
      H_endpoint_one, Finset.Ico_eq_empty (by omega), Finset.sum_empty, Nat.add_zero]
  · -- `ℓ ≥ 2`: the ranks `0` and `j` are the two endpoints.
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hE : Eend (j' + 1 + 1) q T = 2 * H q ((j' + 1) :: T) := by
      rw [H_endpoint_two_le (by omega), Nat.add_sub_cancel]
    have htop : H q (nz [j' + 1, j' + 1 - (j' + 1)] ++ T) = H q ((j' + 1) :: T) := by
      rw [Nat.sub_self, nz_two_right_zero (by omega), List.singleton_append]
    have hbot : H q (nz [0, j' + 1 - 0] ++ T) = H q ((j' + 1) :: T) := by
      rw [Nat.sub_zero, nz_two_left_zero (by omega), List.singleton_append]
    have hint : ∀ i ∈ Finset.range j',
        H q (nz [i + 1, j' + 1 - (i + 1)] ++ T)
          = H q ((1 + i) :: (j' + 1 - (1 + i)) :: T) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [nz_two (by omega) (by omega), List.cons_append, List.singleton_append]
      have e1 : i + 1 = 1 + i := by omega
      rw [e1]
    rw [Finset.sum_range_succ, Finset.sum_range_succ', htop, hbot,
      Finset.sum_congr rfl hint, hE, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    ring

/-! ### The two inputs from the other modules

Theorems (B) and (C) of component 3b are `deferred_no_completion` and
`legal_complete_avoids` in `Av12453.TwoThreshold.Semantics`; the counting argument uses
nothing else about them, so it is stated relative to the hypotheses `DeferredHyp` and
`CompleteHyp` recorded in `Av12453.TwoThreshold.Defs`. -/

/-- A letter of a deferred interval contributes nothing to the prefix partition: by (B) it
has no `12453`-avoiding completion at all. -/
theorem A_eq_zero_of_deferred (hDef : DeferredHyp) (hleg : Legal n σ) {I : Finset ℕ}
    (hI : I ∈ (stack n σ).tail) (hx : x ∈ I) : A n (σ ++ [x]) = 0 := by
  rw [A, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro w hw ⟨hpre, hav⟩
  exact hav (hDef n σ x hleg I hI hx w (mem_perms.mp hw) hpre)

/-! ### The base case of the induction: no unread values left -/

/-- With no unread values the prefix is a complete legal word, so by (C) it avoids `12453`
and is counted once; on the other side `ρ = 0` forces the state to be `((0,0), ∅)`, and
`H_𝟎(∅) = 1` is the terminal condition of \eqref{eq:initial-terminal}. -/
theorem A_eq_H_base (hCplt : CompleteHyp) (hleg : Legal n σ)
    (h0 : (unread n σ).card = 0) : A n σ = H (p n σ) (L n σ) := by
  have hw : IsWord n σ := hleg.isWord
  have hlen : σ.length = n := by
    have h1 := card_unread hw
    have h2 := hw.length_le
    omega
  have hρ := rho_eq hleg
  have hp : p n σ = (0, 0) := by
    have h1 : (p n σ).1 = 0 := by omega
    have h2 : (p n σ).2 = 0 := by omega
    exact Prod.ext h1 h2
  have hLnil : L n σ = [] := by
    cases hLc : L n σ with
    | nil => rfl
    | cons a t =>
      have ha : 0 < a := L_pos hleg a (by rw [hLc]; exact List.mem_cons_self)
      rw [hLc, List.sum_cons] at hρ
      omega
  rw [A_complete n σ hw hlen, if_pos (hCplt n σ hleg hlen), hp, hLnil, H_zero]

/-! ### (D): the recurrence counts the completions -/

/--
**(D)** relative to theorems (B) and (C).  For every legal prefix `σ` the number of
`12453`-avoiding permutations of `{0, …, n-1}` extending `σ` is `H (p n σ) (L n σ)`.

The induction runs on `(unread n σ).card = p₀ + p₁ + |L n σ|`, the paper's `ρ` of
\eqref{eq:rho} (`rho_eq`), which drops by one at every move (`card_unread_succ`).  In the
inductive step the prefix partition `A_succ` splits the unread values into the two bands
`B₀`, `B₁` and the values above `b₂` (`sum_unread_split`); the last group is, by the layout
invariant, the union of the intervals of the stack.  The band letters reindex to
`h = 0, …, p_i - 1` by `sum_below0_eq`/`sum_below1_eq` and give lines 1 and 2 of
\eqref{eq:H} through the transitions \eqref{eq:T} and \eqref{eq:U}; among the letters above
`b₂`, those of the active head reindex to their local ranks by `sum_rank_eq` and give lines
3 and 4 by `sum_rank_split`, while those of the deferred intervals contribute `0` by (B).
-/
theorem A_eq_H_of (hDef : DeferredHyp) (hCplt : CompleteHyp) {n : ℕ} :
    ∀ σ : List ℕ, Legal n σ → A n σ = H (p n σ) (L n σ) := by
  suffices key : ∀ (k : ℕ) (σ : List ℕ), (unread n σ).card ≤ k → Legal n σ →
      A n σ = H (p n σ) (L n σ) from fun σ hleg => key _ σ le_rfl hleg
  intro k
  induction k with
  | zero => exact fun σ hcard hleg => A_eq_H_base hCplt hleg (Nat.le_zero.mp hcard)
  | succ k ih =>
    intro σ hcard hleg
    rcases Nat.eq_zero_or_pos (unread n σ).card with h0 | hpos
    · exact A_eq_H_base hCplt hleg h0
    have hw : IsWord n σ := hleg.isWord
    have hlay : Layout n σ := layout_of_legal hleg
    have hlen : σ.length < n := by
      have h1 := card_unread hw
      have h2 := hw.length_le
      omega
    -- the inductive hypothesis, available at every legal successor
    have IH : ∀ y : ℕ, Legal n (σ ++ [y]) →
        A n (σ ++ [y]) = H (p n (σ ++ [y])) (L n (σ ++ [y])) := by
      intro y hy
      refine ih (σ ++ [y]) ?_ hy
      have := card_unread_succ hy
      omega
    -- \eqref{eq:H}'s three groups of next letters: band `0`, band `1`, above `b₂`
    rw [A_succ n σ hlen, sum_unread_split (fun y => A n (σ ++ [y]))]
    -- line 1 of \eqref{eq:H}: the early-band letters, reindexed by `h = below0`
    have hband0 : ∑ y ∈ B0 n σ, A n (σ ++ [y])
        = ∑ h ∈ Finset.range (p n σ).1,
            H (h, (p n σ).2 + (p n σ).1 - 1 - h) (L n σ) := by
      have hterm : ∀ y ∈ B0 n σ, A n (σ ++ [y])
          = (fun h => H (h, (p n σ).2 + (p n σ).1 - 1 - h) (L n σ)) (below0 n σ y) := by
        intro y hy
        obtain ⟨hleg', hp', hL'⟩ := pL_succ_band0 hleg hy
        rw [IH y hleg', hp', hL']
      rw [Finset.sum_congr rfl hterm]
      exact sum_below0_eq (fun h => H (h, (p n σ).2 + (p n σ).1 - 1 - h) (L n σ))
    cases hst : stack n σ with
    | nil =>
      -- An empty stack: no letter above `b₂` is legal, and \eqref{eq:H} is `H_eq_nil`.
      have hCempty : (unread n σ).filter (fun y => b2 n σ < y) = ∅ := by
        rw [← hlay.union, hst]
        simp [stackUnion]
      have hLnil : L n σ = [] := by rw [L, hst, List.map_nil]
      have hρ := rho_eq hleg
      rw [hLnil, List.sum_nil, Nat.add_zero] at hρ
      -- line 2 of \eqref{eq:H} at an empty stack: `ℓ₁ = 0`, so `\nz` deletes an empty `E`
      have hband1 : ∑ y ∈ B1 n σ, A n (σ ++ [y])
          = ∑ h ∈ Finset.range (p n σ).2,
              H ((p n σ).1, h) (nz [(p n σ).2 - 1 - h]) := by
        have hterm : ∀ y ∈ B1 n σ, A n (σ ++ [y])
            = (fun h => H ((p n σ).1, h) (nz [(p n σ).2 - 1 - h])) (below1 n σ y) := by
          intro y hy
          obtain ⟨hleg', hp', hL'⟩ := pL_succ_band1_nil hleg hst hy
          rw [IH y hleg', hp', hL']
        rw [Finset.sum_congr rfl hterm]
        exact sum_below1_eq (fun h => H ((p n σ).1, h) (nz [(p n σ).2 - 1 - h]))
      have hpne : p n σ ≠ (0, 0) := by
        intro hc
        have h1 : (p n σ).1 = 0 := by rw [hc]
        have h2 : (p n σ).2 = 0 := by rw [hc]
        omega
      rw [hband0, hband1, hCempty, Finset.sum_empty, Nat.add_zero, hLnil,
        H_eq_nil (p n σ), if_neg hpne]
      omega
    | cons I₁ tail =>
      -- A nonempty stack: all four lines of \eqref{eq:H}, plus the deferred letters.
      have hI₁mem : I₁ ∈ stack n σ := by rw [hst]; exact List.mem_cons_self
      have hLcons : L n σ = I₁.card :: tail.map Finset.card := by
        rw [L, hst, List.map_cons]
      have hℓpos : 1 ≤ I₁.card := Finset.card_pos.mpr (hlay.nonempty I₁ hI₁mem)
      have hI₁gt : ∀ y ∈ I₁, b2 n σ < y := fun y hy => hlay.lt_of_mem hI₁mem hy
      have hI₁unread : ∀ y ∈ I₁, y ∈ unread n σ := fun y hy => hlay.unread_of_mem hI₁mem hy
      have hI₁sub : I₁ ⊆ (unread n σ).filter (fun y => b2 n σ < y) := fun y hy =>
        Finset.mem_filter.mpr ⟨hI₁unread y hy, hI₁gt y hy⟩
      -- line 2 of \eqref{eq:H}: the last-band letters, reindexed by `h = below1`;
      -- `E` merges into the head, which has `ℓ₁ ≥ 1`, so `\nz` is not needed
      have hband1 : ∑ y ∈ B1 n σ, A n (σ ++ [y])
          = ∑ h ∈ Finset.range (p n σ).2,
              H ((p n σ).1, h) ((I₁.card + ((p n σ).2 - 1 - h)) :: tail.map Finset.card) := by
        have hterm : ∀ y ∈ B1 n σ, A n (σ ++ [y])
            = (fun h => H ((p n σ).1, h)
                ((I₁.card + ((p n σ).2 - 1 - h)) :: tail.map Finset.card)) (below1 n σ y) := by
          intro y hy
          obtain ⟨hleg', hp', hL'⟩ := pL_succ_band1_cons hleg hst hy
          rw [IH y hleg', hp', hL']
        rw [Finset.sum_congr rfl hterm]
        exact sum_below1_eq (fun h => H ((p n σ).1, h)
          ((I₁.card + ((p n σ).2 - 1 - h)) :: tail.map Finset.card))
      -- the deferred letters contribute nothing, by (B)
      have hCsplit : ∑ y ∈ (unread n σ).filter (fun y => b2 n σ < y), A n (σ ++ [y])
          = ∑ y ∈ I₁, A n (σ ++ [y]) := by
        rw [← Finset.sum_sdiff hI₁sub]
        have hzero : ∑ y ∈ ((unread n σ).filter (fun y => b2 n σ < y)) \ I₁,
            A n (σ ++ [y]) = 0 := by
          refine Finset.sum_eq_zero fun y hy => ?_
          rw [Finset.mem_sdiff, Finset.mem_filter] at hy
          obtain ⟨⟨hyu, hyb⟩, hyI₁⟩ := hy
          obtain ⟨J, hJ, hyJ⟩ := hlay.exists_mem hyu hyb
          rw [hst, List.mem_cons] at hJ
          rcases hJ with rfl | hJ
          · exact absurd hyJ hyI₁
          · exact A_eq_zero_of_deferred hDef hleg (I := J)
              (by rw [hst, List.tail_cons]; exact hJ) hyJ
        rw [hzero, Nat.zero_add]
      -- lines 3 and 4: the active head, reindexed by local rank
      have hhead : ∑ y ∈ I₁, A n (σ ++ [y])
          = ∑ r ∈ Finset.range I₁.card,
              H (p n σ) (nz [r, I₁.card - 1 - r] ++ tail.map Finset.card) := by
        have hterm : ∀ y ∈ I₁, A n (σ ++ [y])
            = (fun r => H (p n σ) (nz [r, I₁.card - 1 - r] ++ tail.map Finset.card))
                ((I₁.filter (· < y)).card) := by
          intro y hy
          obtain ⟨hleg', hp', hL'⟩ :=
            pL_succ_active hleg hst (hI₁unread y hy) (hI₁gt y hy) hy
          rw [IH y hleg', hp', hL']
        rw [Finset.sum_congr rfl hterm]
        exact sum_rank_eq I₁
          (fun r => H (p n σ) (nz [r, I₁.card - 1 - r] ++ tail.map Finset.card))
      -- \eqref{eq:H} at the state `(𝐩, ℓ₁ :: L')` of `σ`, expanded once
      have hRHS : H (p n σ) (L n σ) =
          (∑ h ∈ Finset.range (p n σ).1,
              H (h, (p n σ).2 + (p n σ).1 - 1 - h) (I₁.card :: tail.map Finset.card))
            + (∑ h ∈ Finset.range (p n σ).2,
                H ((p n σ).1, h)
                  ((I₁.card + ((p n σ).2 - 1 - h)) :: tail.map Finset.card))
            + Eend I₁.card (p n σ) (tail.map Finset.card)
            + ∑ a ∈ Finset.Ico 1 (I₁.card - 1),
                H (p n σ) (a :: (I₁.card - 1 - a) :: tail.map Finset.card) := by
        rw [hLcons, H_eq_cons hℓpos]
      have hband0' : ∑ y ∈ B0 n σ, A n (σ ++ [y])
          = ∑ h ∈ Finset.range (p n σ).1,
              H (h, (p n σ).2 + (p n σ).1 - 1 - h) (I₁.card :: tail.map Finset.card) := by
        rw [hband0, hLcons]
      rw [hband0', hband1, hCsplit, hhead,
        sum_rank_split (p n σ) (tail.map Finset.card) I₁.card hℓpos, hRHS]
      omega

/-- **The goal of component 3b**, relative to theorems (B) and (C): the recurrence `H` at
the initial state `((n, 0), ∅)` of \eqref{eq:initial-terminal} counts the `12453`-avoiding
permutations of `{0, …, n-1}`. -/
theorem av12453_count_of (hDef : DeferredHyp) (hCplt : CompleteHyp) (n : ℕ) :
    H (n, 0) [] = (avoiders n (beta 2)).card := by
  have h := A_eq_H_of hDef hCplt (n := n) [] Legal_nil
  rw [p_nil, L_nil] at h
  rw [← h, A_nil]

/-! ### Positivity of `H`, and legality as "prefix of a `12453`-avoider"

Theorems (A)--(D) are stated for a *legal* prefix, as \cref{cor:separators} and
\cref{prop:state-invariant} now are; the paper identifies the legal prefixes with the
prefixes of `12453`-avoiding permutations in \cref{prop:scan-states}(c).  This section
proves the half that (D) supplies: every legal prefix has an avoiding completion, so the
paper's remark before \cref{cor:separators} -- "every legal prefix has an avoiding
completion, so condition (iii) below is not vacuous" -- holds at `d = 2`.
(The converse, "every prefix of an avoider is legal", is theorem (B) applied along the scan;
it is stated here relative to `DeferredHyp` as `legal_of_prefix_avoider_of`, following the
recommendation of the component-3a report (development notes, in git history) §11, where the `d
= 1` versions were added
in phase 3.)

The engine is `H_pos`, which formalizes the maximal recurrence path exhibited in the proof of
\cref{prop:scan-states}(c) (and reused by \cref{cor:separators}, (iii) implies (i)): read the
base values in decreasing order -- each is
the largest one remaining, so it either updates `b₁` (the early-band branch, `h = p₀ - 1`,
which lands on the control `(p₀-1, 0)`) or becomes the least `2`-trigger with `δ_h = 0` (the
last-band branch, `h = p₁ - 1`, whose merger set is empty and is deleted by `\nz`) -- and then
take endpoint choices until the stack is exhausted.  Every step is a transition of
\eqref{eq:H} and `ρ` drops by one, so the path reaches `H_𝟎(∅) = 1`. -/

private theorem H_pos_aux : ∀ (k : ℕ) (q : ℕ × ℕ) (l : List ℕ), q.1 + q.2 + l.sum ≤ k →
    (∀ a ∈ l, 0 < a) → 0 < H q l := by
  intro k
  induction k with
  | zero =>
    intro q l hle hpos
    obtain rfl : l = [] := by
      cases l with
      | nil => rfl
      | cons a t =>
        have ha : 0 < a := hpos a List.mem_cons_self
        rw [List.sum_cons] at hle
        omega
    obtain rfl : q = (0, 0) := by
      have h1 : q.1 = 0 := by simp only [List.sum_nil] at hle; omega
      have h2 : q.2 = 0 := by simp only [List.sum_nil] at hle; omega
      exact Prod.ext h1 h2
    rw [H_zero]
    exact Nat.one_pos
  | succ k ih =>
    intro q l hle hpos
    cases l with
    | nil =>
      rw [List.sum_nil, Nat.add_zero] at hle
      rw [H_eq_nil]
      by_cases hq : q = (0, 0)
      · rw [if_pos hq]
        omega
      · rcases Nat.eq_zero_or_pos q.2 with h2 | h2
        · -- the early band: read the largest band-`0` value, `h = p₀ - 1`
          have h1 : 0 < q.1 := by
            rcases Nat.eq_zero_or_pos q.1 with h1 | h1
            · exact absurd (Prod.ext h1 h2) hq
            · exact h1
          refine lt_of_lt_of_le ?_ (Nat.le_add_right _ _)
          refine lt_of_lt_of_le ?_ (Nat.le_add_left _ _)
          refine Finset.sum_pos' (fun i _ => Nat.zero_le _)
            ⟨q.1 - 1, Finset.mem_range.mpr (by omega), ?_⟩
          have hz : q.2 + q.1 - 1 - (q.1 - 1) = 0 := by omega
          rw [hz]
          exact ih (q.1 - 1, 0) [] (by simp; omega) (by simp)
        · -- the last band: read the largest band-`1` value, `h = p₁ - 1`, so `δ_h = 0`
          refine lt_of_lt_of_le ?_ (Nat.le_add_left _ _)
          refine Finset.sum_pos' (fun i _ => Nat.zero_le _)
            ⟨q.2 - 1, Finset.mem_range.mpr (by omega), ?_⟩
          have hz : q.2 - 1 - (q.2 - 1) = 0 := by omega
          rw [hz, nz_singleton, if_pos rfl]
          exact ih (q.1, q.2 - 1) [] (by simp; omega) (by simp)
    | cons ℓ L' =>
      -- a nonempty stack: an endpoint choice always exists
      have hℓ : 0 < ℓ := hpos ℓ List.mem_cons_self
      have hL' : ∀ a ∈ L', 0 < a := fun a ha => hpos a (List.mem_cons_of_mem _ ha)
      rw [List.sum_cons] at hle
      rw [H_eq_cons hℓ]
      have hE : 0 < Eend ℓ q L' := by
        by_cases h1 : ℓ = 1
        · rw [Eend, if_pos h1]
          exact ih q L' (by omega) hL'
        · rw [Eend, if_neg h1]
          have hlt : 0 < H q ((ℓ - 1) :: L') := by
            refine ih q _ ?_ ?_
            · rw [List.sum_cons]; omega
            · intro a ha
              rcases List.mem_cons.mp ha with rfl | ha
              · omega
              · exact hL' a ha
          omega
      omega

/-- **`H` is positive** at every control and every composition with positive parts: every
such state has at least one maximal transition sequence, namely the greedy base moves
followed by the endpoint moves described in the proof of \cref{prop:scan-states}(c). -/
theorem H_pos (q : ℕ × ℕ) (l : List ℕ) (hl : ∀ a ∈ l, 0 < a) : 0 < H q l :=
  H_pos_aux _ q l le_rfl hl

/-- **Every legal prefix has a `12453`-avoiding completion**, so \cref{cor:separators}(iii)
is not vacuous at `d = 2`.  Relative to (B) and (C), through (D). -/
theorem exists_completion_of_legal_of (hDef : DeferredHyp) (hCplt : CompleteHyp)
    (hleg : Legal n σ) : ∃ w, IsPermOf n w ∧ Avoids w (beta 2) ∧ σ <+: w := by
  have h : 0 < A n σ := by
    rw [A_eq_H_of hDef hCplt σ hleg]
    exact H_pos _ _ (L_pos hleg)
  rw [A, Finset.card_pos] at h
  obtain ⟨w, hw⟩ := h
  rw [Finset.mem_filter, mem_perms] at hw
  exact ⟨w, hw.1, hw.2.2, hw.2.1⟩

/-- **Every prefix of a `12453`-avoiding permutation is legal**: the scan of an avoider never
reaches a deferred interval, by (B).  Relative to (B). -/
theorem legal_of_prefix_avoider_of (hDef : DeferredHyp) {w : List ℕ} (hw : IsPermOf n w)
    (hav : Avoids w (beta 2)) (hpre : σ <+: w) : Legal n σ := by
  have hnd : w.Nodup := hw.nodup
  have hall : ∀ y ∈ w, y < n := fun y hy => List.mem_range.mp (hw.mem_iff.mp hy)
  have key : ∀ k : ℕ, Legal n (w.take k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      by_cases hk : k < w.length
      · have hτ : Legal n (w.take k) := ih
        have hlay : Layout n (w.take k) := layout_of_legal hτ
        have hsplit : w.take (k + 1) = w.take k ++ [w.getD k 0] :=
          OneThreshold.take_succ_eq hk
        have hval : w.getD k 0 = w[k]'hk := List.getD_eq_getElem _ _ hk
        have hxun : w.getD k 0 ∈ unread n (w.take k) := by
          rw [hval]
          exact mem_unread.mpr ⟨hall _ (List.getElem_mem hk),
            OneThreshold.getElem_notMem_take hnd hk le_rfl⟩
        have hxb2 : w.getD k 0 ≠ b2 n (w.take k) := fun hc =>
          b2_not_unread n (w.take k) (hc ▸ hxun)
        rw [hsplit]
        cases hst : stack n (w.take k) with
        | nil =>
          rw [legal_succ_iff_nil hτ hst]
          refine ⟨hxun, ?_⟩
          by_contra hge
          have hmem : w.getD k 0 ∈ stackUnion (stack n (w.take k)) := by
            rw [hlay.union]
            exact Finset.mem_filter.mpr ⟨hxun, by omega⟩
          rw [hst] at hmem
          simp [stackUnion] at hmem
        | cons I₁ tail =>
          rw [legal_succ_iff_cons hτ hst]
          refine ⟨hxun, ?_⟩
          by_cases hlt : w.getD k 0 < b2 n (w.take k)
          · exact Or.inl hlt
          · refine Or.inr ?_
            obtain ⟨I, hI, hxI⟩ := hlay.exists_mem hxun (by omega)
            rw [hst, List.mem_cons] at hI
            rcases hI with rfl | hI
            · exact hxI
            · refine absurd ?_ hav
              refine hDef n (w.take k) _ hτ I (by rw [hst, List.tail_cons]; exact hI) hxI
                w hw ?_
              rw [← hsplit]
              exact List.take_prefix _ _
      · have h1 : w.take (k + 1) = w := List.take_of_length_le (by omega)
        have h2 : w.take k = w := List.take_of_length_le (by omega)
        rw [h1, ← h2]
        exact ih
  have := key σ.length
  rwa [← List.prefix_iff_eq_take.mp hpre] at this

/-- **\cref{prop:scan-states}(c) at `d = 2`**, which is also the hypothesis of
\cref{cor:separators} and \cref{prop:state-invariant}: `σ` is a legal prefix of the
two-threshold scan if and only if it is an initial segment of some `12453`-avoiding
permutation of `{0, …, n-1}`.  Relative to (B) and (C). -/
theorem legal_iff_prefix_avoider_of (hDef : DeferredHyp) (hCplt : CompleteHyp) :
    Legal n σ ↔ ∃ w, IsPermOf n w ∧ Avoids w (beta 2) ∧ σ <+: w :=
  ⟨exists_completion_of_legal_of hDef hCplt,
    fun ⟨_, hw, hav, hpre⟩ => legal_of_prefix_avoider_of hDef hw hav hpre⟩

/-! ### Discharging (B) and (C)

`Av12453.TwoThreshold.Semantics` proves the two hypotheses, under the frozen names
`deferred_no_completion` and `legal_complete_avoids`; the two theorems below are the `_of`
forms above with those supplied.  Both bodies are exactly the ones that discharged
`DeferredHyp`/`CompleteHyp` in `Av12453.OneThreshold.Counting`, with `beta 1` replaced by
`beta 2`; the `_of` forms are what makes them one-liners. -/

/-- **(D)**, with theorems (B) and (C) supplied by `Av12453.TwoThreshold.Semantics`: the
number of `12453`-avoiding completions of a legal prefix `σ` is the value of the literal
recurrence \eqref{eq:H} at the state `(𝐩, L)` the two-threshold scan has reached.  This is
\cref{thm:literal} at `d = 2`. -/
theorem A_eq_H (hleg : Legal n σ) : A n σ = H (p n σ) (L n σ) :=
  A_eq_H_of (fun _ _ _ h _ hI hx _ hw hpre => deferred_no_completion h hI hx hw hpre)
    (fun _ _ h hl => legal_complete_avoids h hl) σ hleg

/-- **The goal of component 3b**: the literal recurrence \eqref{eq:H} at `d = 2`, started
from the initial state `𝐩 = (n, 0)` with the empty stack (\eqref{eq:initial-terminal}),
counts the `12453`-avoiding permutations of `{0, …, n-1}`. -/
theorem av12453_count (n : ℕ) : H (n, 0) [] = (avoiders n (beta 2)).card :=
  av12453_count_of (fun _ _ _ h _ hI hx _ hw hpre => deferred_no_completion h hI hx hw hpre)
    (fun _ _ h hl => legal_complete_avoids h hl) n

/-- **(B) packaged as `DeferredHyp`**, unconditionally. -/
theorem deferredHyp : DeferredHyp := deferredHyp_of_sep sepInvariant

/-- **(C) packaged as `CompleteHyp`**, unconditionally. -/
theorem completeHyp : CompleteHyp := completeHyp_of_sep sepInvariant

/-- **Every legal prefix has a `12453`-avoiding completion**, so \cref{cor:separators}(iii)
is not vacuous at `d = 2`.  This is the paper's remark before \cref{cor:separators}. -/
theorem exists_completion_of_legal (hleg : Legal n σ) :
    ∃ w, IsPermOf n w ∧ Avoids w (beta 2) ∧ σ <+: w :=
  exists_completion_of_legal_of deferredHyp completeHyp hleg

/-- **Every prefix of a `12453`-avoiding permutation is legal.** -/
theorem legal_of_prefix_avoider {w : List ℕ} (hw : IsPermOf n w) (hav : Avoids w (beta 2))
    (hpre : σ <+: w) : Legal n σ :=
  legal_of_prefix_avoider_of deferredHyp hw hav hpre

/-- **\cref{prop:scan-states}(c) at `d = 2`**, which is also the hypothesis of
\cref{cor:separators} and \cref{prop:state-invariant}: `σ` is a legal prefix of the
two-threshold scan if and only if it is an initial segment of some `12453`-avoiding
permutation of `{0, …, n-1}`.  This is what makes the Lean development's "legal prefix" and
the paper's "prefix of a `β₂`-avoiding permutation" the same class of words. -/
theorem legal_iff_prefix_avoider :
    Legal n σ ↔ ∃ w, IsPermOf n w ∧ Avoids w (beta 2) ∧ σ <+: w :=
  legal_iff_prefix_avoider_of deferredHyp completeHyp

/-! ### Numerical cross-check

The two sides of `av12453_count_of` are independently computable: the left-hand side runs
the recurrence \eqref{eq:H}, the right-hand side filters `k!` words by `Contains _ (beta 2)`.
They agree on the first eight terms `1, 1, 2, 6, 24, 119, 694, 4581` of `|Av_k(12453)|`
(`code/data/av12453_terms_0_300.txt`, the paper's \eqref{eq:first-terms}).  This is an
`#eval`, not a `decide`: `perms` goes through `List.permutations`, which the kernel does not
reduce, so it proves nothing on its own -- but `#guard_msgs` fails the build if the output
ever changes, which makes it a live regression check on both implementations at once. -/

set_option linter.hashCommand false in
/-- info: [(1, 1), (1, 1), (2, 2), (6, 6), (24, 24), (119, 119), (694, 694), (4581, 4581)] -/
#guard_msgs in
#eval (List.range 8).map (fun k => ((avoiders k (beta 2)).card, H (k, 0) []))

end TwoThreshold
end Av12453
