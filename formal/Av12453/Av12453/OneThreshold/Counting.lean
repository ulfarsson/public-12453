/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Av12453.OneThreshold.Semantics

/-!
# Component 3a, theorem (D): the recurrence counts the completions

This module proves the counting half of the one-threshold construction: for every legal
prefix `σ`, the number `A n σ` of `1342`-avoiding permutations of `{0, …, n-1}` beginning
with `σ` equals `W (p n σ) (L n σ)`, the paper's `W_p(L)` evaluated at the abstract state of
`σ`.  Specializing to `σ = []` gives `W n ∅ = |Av_n(1342)|`, the goal of component 3a.

The proof is the induction of \cref{prop:scalar-literal} (and of \cref{cor:separators}'s
`d = 1` specialization), run on the measure `ρ₁ = p + |L| = |unread|` of
\eqref{eq:rho-scalar}, which drops by one at every move (`card_unread_succ`).  The prefix
partition `A_succ` writes `A n σ` as a sum over the unread values, and that sum is
regrouped exactly as the paper's proof regroups it:

* the **base letters**, the unread values below the threshold `m`, indexed by the number
  `h` of unread values below them, `h = 0, …, p-1` (`sum_below_eq`); each contributes
  `W h ((ℓ₁ + p - 1 - h) :: L')`, or `W h (nz (p-1-h))` when the stack is empty;
* the **active-head letters**, indexed by their local rank `r = 0, …, ℓ₁-1`
  (`sum_rank_eq`); the two endpoints `r = 0` and `r = ℓ₁-1` give the endpoint term
  `E_{ℓ₁}(p, L')` of \eqref{eq:W-endpoint} (two letters when `ℓ₁ ≥ 2`, one when `ℓ₁ = 1`),
  and each interior rank gives one term of the last line of \eqref{eq:W};
* the **deferred letters**, which contribute `0` by theorem (B).

Theorems (B) and (C) of the component enter only through the two hypotheses `DeferredHyp`
and `CompleteHyp`; `A_eq_W_of` is stated relative to them, so that it is axiom-clean, and
`A_eq_W`/`av1342_count` discharge them with the theorems of the same name proved in
`Av12453.OneThreshold.Semantics`.

## Main results

* `sum_rank_split` : the local-rank sum over the active head is the endpoint term plus the
  interior terms, i.e. the last two lines of \eqref{eq:W}.
* `A_eq_W_of` : **(D-iii)**, relative to (B) and (C).
* `A_eq_W` : **(D-iii)** with (B) and (C) discharged.
* `av1342_count` : **the goal of component 3a**, `W n ∅ = |Av_n(1342)|`.

## Numerical check

Both sides of `av1342_count` are computable, and evaluating them independently with

    #eval (List.range 8).map (fun k => ((avoiders k (beta 1)).card, W k []))

returns `[(1, 1), (1, 1), (2, 2), (6, 6), (23, 23), (103, 103), (512, 512), (2740, 2740)]`,
the first terms of `|Av_n(1342)|` (Bona's sequence; the paper's \eqref{eq:first-terms} is
the `d = 2` sequence of `Av(12453)`, not this one).  (The check is not a `decide`: `perms` goes
through `List.permutations`, which the kernel does not reduce.)
-/

namespace Av12453
namespace OneThreshold

variable {n : ℕ} {σ : List ℕ} {x : ℕ}

/-! ### Deleting zeros from a two-entry list -/

theorem nz_pair {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : nz [a, b] = [a, b] := by
  simp [nz, ha, hb]

theorem nz_pair_left_zero {b : ℕ} (hb : b ≠ 0) : nz [0, b] = [b] := by
  simp [nz, hb]

theorem nz_pair_right_zero {a : ℕ} (ha : a ≠ 0) : nz [a, 0] = [a] := by
  simp [nz, ha]

theorem nz_pair_zero_zero : nz [(0 : ℕ), 0] = [] := by
  simp [nz]

/-! ### The active head: local ranks give the endpoint and interior terms

`sum_rank_split` is the arithmetic heart of the regrouping.  Reading the value of local
rank `r` of an active head of size `ℓ` leaves the two pieces of sizes `r` and `ℓ - 1 - r`,
with empty pieces deleted.  The extreme ranks `r = 0` and `r = ℓ - 1` both leave the single
piece of size `ℓ - 1` -- these are the paper's two endpoints, and they coincide only when
`ℓ = 1`, where there is one endpoint and no piece at all.  The remaining ranks
`r = 1, …, ℓ - 2` leave two nonempty pieces `(a, b)` with `a + b = ℓ - 1`. -/

theorem sum_rank_split (q : ℕ) (T : List ℕ) :
    ∀ ℓ : ℕ, 1 ≤ ℓ →
      ∑ r ∈ Finset.range ℓ, W q (nz [r, ℓ - 1 - r] ++ T)
        = Eend ℓ q T + ∑ a ∈ Finset.Ico 1 (ℓ - 1), W q (a :: (ℓ - 1 - a) :: T) := by
  intro ℓ hℓ
  obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · -- `ℓ = 1`: one endpoint, no interior ranks.
    rw [Finset.sum_range_one, Nat.zero_sub, nz_pair_zero_zero, List.nil_append,
      W_endpoint_one, Finset.Ico_eq_empty (by omega), Finset.sum_empty, Nat.add_zero]
  · -- `ℓ ≥ 2`: the ranks `0` and `j` are the two endpoints.
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hE : Eend (j' + 1 + 1) q T = 2 * W q ((j' + 1) :: T) := by
      rw [W_endpoint_two_le (by omega), Nat.add_sub_cancel]
    have htop : W q (nz [j' + 1, j' + 1 - (j' + 1)] ++ T) = W q ((j' + 1) :: T) := by
      rw [Nat.sub_self, nz_pair_right_zero (by omega), List.singleton_append]
    have hbot : W q (nz [0, j' + 1 - 0] ++ T) = W q ((j' + 1) :: T) := by
      rw [Nat.sub_zero, nz_pair_left_zero (by omega), List.singleton_append]
    have hint : ∀ i ∈ Finset.range j',
        W q (nz [i + 1, j' + 1 - (i + 1)] ++ T)
          = W q ((1 + i) :: (j' + 1 - (1 + i)) :: T) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [nz_pair (by omega) (by omega), List.cons_append, List.singleton_append]
      have e1 : i + 1 = 1 + i := by omega
      rw [e1]
    rw [Finset.sum_range_succ, Finset.sum_range_succ', htop, hbot,
      Finset.sum_congr rfl hint, hE, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    ring

/-! ### The two inputs from the other modules

Theorems (B) and (C) of component 3a are `deferred_no_completion` and
`legal_complete_avoids` in `Av12453.OneThreshold.Semantics`; the counting argument uses
nothing else about them, so it is stated relative to the two hypotheses below. -/

/-- **Hypothesis (B)**: a letter of a deferred interval has no `1342`-avoiding completion.
This is the statement of `deferred_no_completion`. -/
def DeferredHyp : Prop :=
  ∀ (n : ℕ) (σ : List ℕ) (x : ℕ), Legal n σ → ∀ I ∈ (stack n σ).tail, x ∈ I →
    ∀ w : List ℕ, IsPermOf n w → (σ ++ [x]) <+: w → Contains w (beta 1)

/-- **Hypothesis (C)**: a legal word of full length avoids `1342`.  This is the statement of
`legal_complete_avoids`. -/
def CompleteHyp : Prop :=
  ∀ (n : ℕ) (σ : List ℕ), Legal n σ → σ.length = n → Avoids σ (beta 1)

/-- A letter of a deferred interval contributes nothing to the prefix partition. -/
theorem A_eq_zero_of_deferred (hDef : DeferredHyp) (hleg : Legal n σ) {I : Finset ℕ}
    (hI : I ∈ (stack n σ).tail) (hx : x ∈ I) : A n (σ ++ [x]) = 0 := by
  rw [A, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro w hw ⟨hpre, hav⟩
  exact hav (hDef n σ x hleg I hI hx w (mem_perms.mp hw) hpre)

/-! ### The base case of the induction: no unread values left -/

/-- With no unread values the prefix is a complete legal word, so it avoids `1342` and is
counted once; on the other side the state is `(0, ∅)` and `W 0 ∅ = 1`. -/
theorem A_eq_W_base (hCplt : CompleteHyp) (hleg : Legal n σ)
    (h0 : (unread n σ).card = 0) : A n σ = W (p n σ) (L n σ) := by
  have hw : IsWord n σ := hleg.isWord
  have hlen : σ.length = n := by
    have h1 := card_unread hw
    have h2 := hw.length_le
    omega
  have hρ := rho_eq hleg
  have hp0 : p n σ = 0 := by omega
  have hLnil : L n σ = [] := by
    cases hLc : L n σ with
    | nil => rfl
    | cons a t =>
      have ha : 0 < a := L_pos hleg a (by rw [hLc]; exact List.mem_cons_self)
      rw [hLc, List.sum_cons] at hρ
      omega
  rw [A_complete n σ hw hlen, if_pos (hCplt n σ hleg hlen), hp0, hLnil, W_eq_nil]
  simp

/-! ### (D-iii): the recurrence counts the completions -/

/--
**(D-iii)** relative to theorems (B) and (C).  For every legal prefix `σ` the number of
`1342`-avoiding permutations extending `σ` is `W (p n σ) (L n σ)`.

The induction runs on `(unread n σ).card = p n σ + (L n σ).sum`, the paper's `ρ₁` of
\eqref{eq:rho-scalar}.  In the inductive step the prefix partition `A_succ` splits the
unread values into those below the threshold `m` -- the base letters, which reindex to
`h = 0, …, p-1` by `sum_below_eq` and give the first line of \eqref{eq:W} (or
\eqref{eq:W-boundary} when the stack is empty) -- and those above it, which by the layout
invariant are the union of the intervals of the stack.  Of the latter, the letters of the
active head reindex to their local ranks by `sum_rank_eq` and give the endpoint and
interior terms by `sum_rank_split`, while the letters of the deferred intervals contribute
`0` by (B).
-/
theorem A_eq_W_of (hDef : DeferredHyp) (hCplt : CompleteHyp) {n : ℕ} :
    ∀ σ : List ℕ, Legal n σ → A n σ = W (p n σ) (L n σ) := by
  suffices H : ∀ (k : ℕ) (σ : List ℕ), (unread n σ).card ≤ k → Legal n σ →
      A n σ = W (p n σ) (L n σ) from fun σ hleg => H _ σ le_rfl hleg
  intro k
  induction k with
  | zero => exact fun σ hcard hleg => A_eq_W_base hCplt hleg (Nat.le_zero.mp hcard)
  | succ k ih =>
    intro σ hcard hleg
    rcases Nat.eq_zero_or_pos (unread n σ).card with h0 | hpos
    · exact A_eq_W_base hCplt hleg h0
    have hw : IsWord n σ := hleg.isWord
    have hlay : Layout n σ := layout_of_legal hleg
    have hlen : σ.length < n := by
      have h1 := card_unread hw
      have h2 := hw.length_le
      omega
    -- the inductive hypothesis, available at every legal successor
    have IH : ∀ y : ℕ, Legal n (σ ++ [y]) →
        A n (σ ++ [y]) = W (p n (σ ++ [y])) (L n (σ ++ [y])) := by
      intro y hy
      refine ih (σ ++ [y]) ?_ hy
      have := card_unread_succ hy
      omega
    -- split the unread values at the threshold
    have hdisj : Disjoint ((unread n σ).filter (· < m n σ))
        ((unread n σ).filter fun y => m n σ < y) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Finset.mem_filter] at ha hb
      omega
    have hUeq : (unread n σ).filter (· < m n σ) ∪ (unread n σ).filter (fun y => m n σ < y)
        = unread n σ := by
      ext y
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hy, -⟩ | ⟨hy, -⟩) <;> exact hy
      · intro hy
        rcases lt_trichotomy y (m n σ) with h | h | h
        · exact Or.inl ⟨hy, h⟩
        · exact absurd (h ▸ hy) (m_not_unread hw)
        · exact Or.inr ⟨hy, h⟩
    have key : ∑ y ∈ unread n σ, A n (σ ++ [y]) =
        (∑ y ∈ (unread n σ).filter (· < m n σ), A n (σ ++ [y]))
          + ∑ y ∈ (unread n σ).filter (fun y => m n σ < y), A n (σ ++ [y]) := by
      rw [← Finset.sum_union hdisj, hUeq]
    rw [A_succ n σ hlen, key]
    cases hst : stack n σ with
    | nil =>
      -- an empty stack: only new minima, and \eqref{eq:W-boundary}
      have hCempty : (unread n σ).filter (fun y => m n σ < y) = ∅ := by
        rw [← hlay.union, hst]
        simp [stackUnion]
      have hLnil : L n σ = [] := by rw [L, hst, List.map_nil]
      have hρ := rho_eq hleg
      rw [hLnil, List.sum_nil, Nat.add_zero] at hρ
      have hterm : ∀ y ∈ (unread n σ).filter (· < m n σ),
          A n (σ ++ [y]) = W (below n σ y) (nz [p n σ - 1 - below n σ y]) := by
        intro y hy
        rw [Finset.mem_filter] at hy
        obtain ⟨hyu, hylt⟩ := hy
        obtain ⟨hp', hL'⟩ := L_succ_newMin_nil hleg hst hyu hylt
        rw [IH y (legal_succ_of_newMin_nil hleg hst hyu hylt).1, hp', hL']
      rw [hCempty, Finset.sum_empty, Nat.add_zero, Finset.sum_congr rfl hterm,
        sum_below_eq (fun h => W h (nz [p n σ - 1 - h])), hLnil, W_eq_nil,
        if_neg (by omega), Nat.zero_add]
    | cons I₁ tail =>
      -- a nonempty stack: base letters, the two endpoints, the interior letters, deferred
      have hI₁mem : I₁ ∈ stack n σ := by rw [hst]; exact List.mem_cons_self
      have hLcons : L n σ = I₁.card :: tail.map Finset.card := by
        rw [L, hst, List.map_cons]
      have hℓpos : 1 ≤ I₁.card := Finset.card_pos.mpr (hlay.nonempty I₁ hI₁mem)
      have hI₁gt : ∀ y ∈ I₁, m n σ < y := fun y hy => hlay.lt_of_mem hI₁mem hy
      have hI₁unread : ∀ y ∈ I₁, y ∈ unread n σ := fun y hy => hlay.unread_of_mem hI₁mem hy
      have hI₁sub : I₁ ⊆ (unread n σ).filter (fun y => m n σ < y) := fun y hy =>
        Finset.mem_filter.mpr ⟨hI₁unread y hy, hI₁gt y hy⟩
      -- the base letters
      have hbase : ∑ y ∈ (unread n σ).filter (· < m n σ), A n (σ ++ [y])
          = ∑ h ∈ Finset.range (p n σ),
              W h ((I₁.card + p n σ - 1 - h) :: tail.map Finset.card) := by
        have hterm : ∀ y ∈ (unread n σ).filter (· < m n σ),
            A n (σ ++ [y]) = W (below n σ y)
              ((I₁.card + p n σ - 1 - below n σ y) :: tail.map Finset.card) := by
          intro y hy
          rw [Finset.mem_filter] at hy
          obtain ⟨hyu, hylt⟩ := hy
          obtain ⟨hp', hL'⟩ := L_succ_newMin_cons hleg hst hyu hylt hI₁gt
          rw [IH y (legal_succ_of_newMin_cons hleg hst hyu hylt).1, hp', hL']
        rw [Finset.sum_congr rfl hterm]
        exact sum_below_eq
          (fun h => W h ((I₁.card + p n σ - 1 - h) :: tail.map Finset.card))
      -- the deferred letters contribute nothing
      have hCsplit : ∑ y ∈ (unread n σ).filter (fun y => m n σ < y), A n (σ ++ [y])
          = ∑ y ∈ I₁, A n (σ ++ [y]) := by
        rw [← Finset.sum_sdiff hI₁sub]
        have hzero : ∑ y ∈ ((unread n σ).filter (fun y => m n σ < y)) \ I₁,
            A n (σ ++ [y]) = 0 := by
          refine Finset.sum_eq_zero fun y hy => ?_
          rw [Finset.mem_sdiff, Finset.mem_filter] at hy
          obtain ⟨⟨hyu, hym⟩, hyI₁⟩ := hy
          obtain ⟨J, hJ, hyJ⟩ := hlay.exists_mem hyu hym
          rw [hst, List.mem_cons] at hJ
          rcases hJ with rfl | hJ
          · exact absurd hyJ hyI₁
          · exact A_eq_zero_of_deferred hDef hleg (I := J)
              (by rw [hst, List.tail_cons]; exact hJ) hyJ
        rw [hzero, Nat.zero_add]
      -- the active head, reindexed by local rank
      have hhead : ∑ y ∈ I₁, A n (σ ++ [y])
          = ∑ r ∈ Finset.range I₁.card,
              W (p n σ) (nz [r, I₁.card - 1 - r] ++ tail.map Finset.card) := by
        have hterm : ∀ y ∈ I₁, A n (σ ++ [y])
            = W (p n σ) (nz [(I₁.filter (· < y)).card,
                I₁.card - 1 - (I₁.filter (· < y)).card] ++ tail.map Finset.card) := by
          intro y hy
          have hyu : y ∈ unread n σ := hI₁unread y hy
          have hge : ¬ y < m n σ := by have := hI₁gt y hy; omega
          obtain ⟨hp', hL'⟩ := L_succ_active hleg hst hyu hge hy
          rw [IH y (legal_succ_of_active hleg hst hyu hge hy).1, hp', hL']
        rw [Finset.sum_congr rfl hterm]
        exact sum_rank_eq I₁
          (fun r => W (p n σ) (nz [r, I₁.card - 1 - r] ++ tail.map Finset.card))
      rw [hbase, hCsplit, hhead,
        sum_rank_split (p n σ) (tail.map Finset.card) I₁.card hℓpos, hLcons,
        W_eq_cons hℓpos]
      omega

/-- **(D-iii)**, with theorems (B) and (C) supplied by `Av12453.OneThreshold.Semantics`. -/
theorem A_eq_W (hleg : Legal n σ) : A n σ = W (p n σ) (L n σ) :=
  A_eq_W_of (fun _ _ _ h _ hI hx _ hw hpre => deferred_no_completion h hI hx hw hpre)
    (fun _ _ h hl => legal_complete_avoids h hl) σ hleg

/-- **The goal of component 3a**: the recurrence `W` counts `1342`-avoiding permutations. -/
theorem av1342_count (n : ℕ) : W n [] = (avoiders n (beta 1)).card := by
  have h := A_eq_W (n := n) (σ := []) Legal_nil
  rw [p_nil, L_nil] at h
  rw [← h, A_nil]

/-! ### Legality is exactly "prefix of a `1342`-avoiding permutation"

Theorems (A)--(D) are stated for a *legal* prefix, as \cref{lem:1342-separators} and
\cref{cor:separators} now are; the paper identifies the legal prefixes with the prefixes of
`1342`-avoiding permutations in \cref{prop:scan-states}(c).  This section reproves that
identification (`legal_iff_prefix_avoider`): one direction is theorem (B), the other follows
from (D-iii) once `W` is known to be positive at every composition with positive parts. -/

private theorem W_pos_aux : ∀ (k q : ℕ) (l : List ℕ), q + l.sum ≤ k → (∀ a ∈ l, 0 < a) →
    0 < W q l := by
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
    obtain rfl : q = 0 := by simpa using hle
    rw [W_eq_nil]
    simp
  | succ k ih =>
    intro q l hle hpos
    cases l with
    | nil =>
      rw [W_eq_nil]
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · simp
      · refine lt_of_lt_of_le ?_ (Nat.le_add_left _ _)
        refine Finset.sum_pos' (fun i _ => Nat.zero_le _)
          ⟨q - 1, Finset.mem_range.mpr (by omega), ?_⟩
        have hz : q - 1 - (q - 1) = 0 := by omega
        rw [hz, nz_singleton, if_pos rfl]
        rw [List.sum_nil] at hle
        exact ih (q - 1) [] (by simp; omega) (by simp)
    | cons ℓ L' =>
      have hℓ : 0 < ℓ := hpos ℓ List.mem_cons_self
      have hL' : ∀ a ∈ L', 0 < a := fun a ha => hpos a (List.mem_cons_of_mem _ ha)
      rw [List.sum_cons] at hle
      rw [W_eq_cons hℓ]
      have hE : 0 < Eend ℓ q L' := by
        by_cases h1 : ℓ = 1
        · rw [Eend, if_pos h1]
          exact ih q L' (by omega) hL'
        · rw [Eend, if_neg h1]
          have : 0 < W q ((ℓ - 1) :: L') := by
            refine ih q _ ?_ ?_
            · rw [List.sum_cons]; omega
            · intro a ha
              rcases List.mem_cons.mp ha with rfl | ha
              · omega
              · exact hL' a ha
          omega
      omega

/-- **`W` is positive** at every control and every composition with positive parts: every
such state has at least one maximal transition sequence, namely the endpoint moves. -/
theorem W_pos (q : ℕ) (l : List ℕ) (hl : ∀ a ∈ l, 0 < a) : 0 < W q l :=
  W_pos_aux _ q l le_rfl hl

/-- **Every legal prefix has a `1342`-avoiding completion.** -/
theorem exists_completion_of_legal (hleg : Legal n σ) :
    ∃ w, IsPermOf n w ∧ Avoids w (beta 1) ∧ σ <+: w := by
  have h : 0 < A n σ := by
    rw [A_eq_W hleg]
    exact W_pos _ _ (L_pos hleg)
  rw [A, Finset.card_pos] at h
  obtain ⟨w, hw⟩ := h
  rw [Finset.mem_filter, mem_perms] at hw
  exact ⟨w, hw.1, hw.2.2, hw.2.1⟩

/-- **Every prefix of a `1342`-avoiding permutation is legal.** -/
theorem legal_of_prefix_avoider {w : List ℕ} (hw : IsPermOf n w) (hav : Avoids w (beta 1))
    (hpre : σ <+: w) : Legal n σ := by
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
        have hsplit : w.take (k + 1) = w.take k ++ [w.getD k 0] := take_succ_eq hk
        have hval : w.getD k 0 = w[k]'hk := List.getD_eq_getElem _ _ hk
        have hxun : w.getD k 0 ∈ unread n (w.take k) := by
          rw [hval]
          exact mem_unread.mpr ⟨hall _ (List.getElem_mem hk),
            getElem_notMem_take hnd hk le_rfl⟩
        have hxm : w.getD k 0 ≠ m n (w.take k) := by
          intro hcon
          exact m_not_unread hτ.isWord (hcon ▸ hxun)
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
          by_cases hlt : w.getD k 0 < m n (w.take k)
          · exact Or.inl hlt
          · refine Or.inr ?_
            obtain ⟨I, hI, hxI⟩ := hlay.exists_mem hxun (by omega)
            rw [hst, List.mem_cons] at hI
            rcases hI with rfl | hI
            · exact hxI
            · refine absurd ?_ hav
              refine deferred_no_completion hτ (I := I) (by rw [hst, List.tail_cons]; exact hI)
                hxI hw ?_
              rw [← hsplit]
              exact List.take_prefix _ _
      · have h1 : w.take (k + 1) = w := List.take_of_length_le (by omega)
        have h2 : w.take k = w := List.take_of_length_le (by omega)
        rw [h1, ← h2]
        exact ih
  have := key σ.length
  rwa [← List.prefix_iff_eq_take.mp hpre] at this

/-- **\cref{prop:scan-states}(c) at `d = 1`**, which is also the hypothesis of
\cref{lem:1342-separators}: `σ` is a legal prefix of the scan if and only if it is an
initial segment of some `1342`-avoiding permutation of `{0, …, n-1}`. -/
theorem legal_iff_prefix_avoider :
    Legal n σ ↔ ∃ w, IsPermOf n w ∧ Avoids w (beta 1) ∧ σ <+: w :=
  ⟨exists_completion_of_legal, fun ⟨_, hw, hav, hpre⟩ => legal_of_prefix_avoider hw hav hpre⟩

end OneThreshold
end Av12453
