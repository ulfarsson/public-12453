/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Av12453.OneThreshold.Defs

/-!
# Patience thresholds and bands for the two-threshold scan

This file is the *threshold API* of the two-threshold scan (`d = 2`, `β₂ = 12453`,
`0`-based `[0, 1, 3, 4, 2]`).  It formalizes \cref{sec:frontier} of the paper
*Protected tails and polynomial-time enumeration of permutations avoiding a direct sum of an
increasing pattern and 231* at `d = 2`: the patience-sorting
thresholds `b₁ < b₂`, the two bands `B₀`, `B₁`, the control `p = (|B₀|, |B₁|)`,
\cref{lem:least-trigger-frontier}, and the effect of one letter on all of them.

Values and positions are `0`-based, as in `Av12453.Basic`.  The paper's *virtual*
thresholds `n + 1`, `n + 2` are here `n` and `n + 1`; the brief for component 3b allows any
values `≥ n` with `b₁ < b₂`, and these two are the ones that make `b₁` literally the `m` of
the one-threshold development (`Av12453.OneThreshold.m`).

## The objects

For a prefix `σ` of a word on `{0, …, n-1}`:

* `b1 n σ` is the least letter of `σ`, with the virtual value `n` when `σ = []`.  It is
  *definitionally* `Av12453.OneThreshold.m n σ` (`b1_eq_m`), so the one-threshold lemmas
  about `m` apply verbatim.
* `b2 n σ` is the least value of a `2`-trigger of `σ` -- the least letter of `σ` that has a
  strictly smaller letter before it -- with the virtual value `n + 1` when `σ` has no
  `2`-trigger.  It is computed as the minimum of the list `trigVals σ` of `2`-trigger
  values together with `n + 1`.
* `B0 n σ` is the set of unread values below `b₁`, `B1 n σ` the set of unread values
  strictly between `b₁` and `b₂` (the paper's bands `B_0` and `B_{d-1}` at `d = 2`), and
  `p n σ = ((B0 n σ).card, (B1 n σ).card)` is the paper's control `𝐩 = (p₀, p₁)`.
* `below0 n σ x`, `below1 n σ x` count the values of `B0`, resp. `B1`, strictly below `x`;
  these are the paper's index `h` in \eqref{eq:T} and \eqref{eq:U}.

## Main definitions

* `Trig2At`, `trigVals` : `2`-triggers by position and the list of their values.
* `b1`, `b2` : the patience-sorting thresholds, virtual values `n` and `n + 1`.
* `B0`, `B1`, `p`, `below0`, `below1` : the bands, the control and the in-band ranks.

## Main results

* `trig2At_iff`, `mem_trigVals_iff` : `Trig2At σ j ↔ IsTriggerAt σ 2 j` and
  `y ∈ trigVals σ ↔ IsTrigger σ 2 y`; with them, `b2` is decidable and computable.
* `isTriggerAt_two_idxOf_iff`, `isTrigger_two_iff` : the `List.idxOf` spelling of "`c` is a
  `2`-trigger" used by \cref{cor:separators}(ii), for a prefix with distinct letters.
* `b1_lt_b2` : `b₁ < b₂`, unconditionally (\cref{sec:frontier}).
* `b1_mem_of_lt`, `b2_mem_of_ne_virtual` : nonvirtual thresholds are read letters;
  `b1_not_unread`, `b2_not_unread`.
* `b2_le_of_isTrigger`, `isTrigger_b2`, `b2_lt_iff_exists_trigger` :
  **\cref{lem:least-trigger-frontier}** -- every `2`-trigger value is `≥ b₂`, and a
  nonvirtual `b₂` is itself the value of a `2`-trigger.
* `thresholds_succ_band0`, `thresholds_succ_band1`, `thresholds_succ_above` : the three
  threshold transitions for `σ ++ [x]` with `x` unread.
* `p_succ_band0`, `p_succ_band1`, `p_succ_above` : the band-count transitions, i.e.
  \eqref{eq:T} at `i = 0` and \eqref{eq:U} at `d = 2`, and the invariance of the control
  under an active-interval move.
* `mem_B0_or_B1_or_gt_b2` : an unread value lies in `B₀`, in `B₁`, or above `b₂`.
* `card_band1_gt`, `filter_between_eq_band1_gt` : the paper's `δ_h = p₁ - 1 - h` of
  \eqref{eq:U} and the set `E` it counts.
* `sum_below0_eq`, `sum_below1_eq` : reindexing a band by the in-band rank, which is how
  \eqref{eq:T} and \eqref{eq:U} turn a sum over letters into a sum over `h`.
-/

namespace Av12453
namespace TwoThreshold

open OneThreshold (unread mem_unread unread_append_singleton IsWord sum_rank_eq
  card_filter_lt_add_card_filter_gt)

variable {n : ℕ} {σ : List ℕ} {a c x y : ℕ}

/-! ### `2`-triggers -/

/-- `Trig2At σ j` : the letter of `σ` in position `j` ends an increasing `2`-subsequence,
i.e. some earlier letter of `σ` is strictly smaller.  This is `Av12453.IsTriggerAt σ 2 j`
written out; see `trig2At_iff`. -/
def Trig2At (σ : List ℕ) (j : ℕ) : Prop :=
  j < σ.length ∧ ∃ i < j, σ.getD i 0 < σ.getD j 0

instance decidableTrig2At (σ : List ℕ) (j : ℕ) : Decidable (Trig2At σ j) := by
  unfold Trig2At; infer_instance

/-- **`2`-triggers are the letters with a smaller letter before them.** -/
theorem trig2At_iff {j : ℕ} : Trig2At σ j ↔ IsTriggerAt σ 2 j := by
  constructor
  · rintro ⟨hj, i, hij, hval⟩
    refine ⟨[i, j], ⟨rfl, ?_, ?_, ?_⟩, rfl⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · omega
      · rw [List.mem_singleton.mp ha]; exact hj
    · simpa using hij
    · simpa using hval
  · rintro ⟨ps, ⟨hlen, hrange, hpos, hval⟩, hlast⟩
    obtain ⟨i, j', rfl⟩ := List.length_eq_two.mp hlen
    have hjj : j' = j := by simpa using hlast
    subst hjj
    have hij : i < j' := by simpa using hpos
    have hvv : σ.getD i 0 < σ.getD j' 0 := by simpa using hval
    exact ⟨hrange j' (by simp), i, hij, hvv⟩

instance decidableIsTriggerAtTwo (σ : List ℕ) (j : ℕ) : Decidable (IsTriggerAt σ 2 j) :=
  decidable_of_iff _ trig2At_iff

/-- The values of the `2`-triggers of `σ`, listed with multiplicity: the letters that have a
strictly smaller letter before them.  Only the set of values matters (`mem_trigVals_iff`);
the list form is what makes `b2` a kernel-computable `foldl`. -/
def trigVals : List ℕ → List ℕ
  | [] => []
  | x :: rest => rest.filter (fun y => decide (x < y)) ++ trigVals rest

@[simp] theorem trigVals_nil : trigVals [] = [] := rfl

theorem trigVals_cons (x : ℕ) (rest : List ℕ) :
    trigVals (x :: rest) = rest.filter (fun y => decide (x < y)) ++ trigVals rest := rfl

/-- **`trigVals` lists exactly the `2`-trigger values.** -/
theorem mem_trigVals_iff_trig2At : y ∈ trigVals σ ↔ ∃ j, Trig2At σ j ∧ σ.getD j 0 = y := by
  induction σ with
  | nil => simp [Trig2At]
  | cons a rest ih =>
    rw [trigVals_cons, List.mem_append, List.mem_filter, ih]
    constructor
    · rintro (⟨hy, hay⟩ | ⟨j, ⟨hj, i, hij, hval⟩, hgy⟩)
      · rw [decide_eq_true_eq] at hay
        obtain ⟨k, hk, hky⟩ := List.getElem_of_mem hy
        refine ⟨k + 1, ⟨by simpa using hk, 0, by omega, ?_⟩, ?_⟩ <;>
          simp [hk, hky, hay]
      · exact ⟨j + 1, ⟨by simpa using hj, i + 1, by omega, by simpa using hval⟩,
          by simpa using hgy⟩
    · rintro ⟨j, ⟨hj, i, hij, hval⟩, hgy⟩
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hk : k < rest.length := by simpa using hj
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · refine Or.inl ⟨?_, ?_⟩
        · rw [← hgy]
          simp [hk]
        · rw [decide_eq_true_eq, ← hgy]
          simpa using hval
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        exact Or.inr ⟨k, ⟨hk, i', by omega, by simpa using hval⟩, by simpa using hgy⟩

/-- **`trigVals` lists exactly the `2`-trigger values**, in the vocabulary of
`Av12453.IsTrigger`. -/
theorem mem_trigVals_iff : y ∈ trigVals σ ↔ IsTrigger σ 2 y := by
  rw [mem_trigVals_iff_trig2At, IsTrigger]
  exact exists_congr fun j => and_congr_left fun _ => trig2At_iff

instance decidableIsTriggerTwo (σ : List ℕ) (c : ℕ) : Decidable (IsTrigger σ 2 c) :=
  decidable_of_iff _ mem_trigVals_iff

/-- Every `2`-trigger value is a letter. -/
theorem mem_of_mem_trigVals (h : y ∈ trigVals σ) : y ∈ σ := by
  obtain ⟨j, ⟨hj, -⟩, rfl⟩ := mem_trigVals_iff_trig2At.mp h
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

/-- Appending one letter creates at most one new `2`-trigger value, namely the new letter,
and only when some earlier letter is smaller. -/
theorem mem_trigVals_append_singleton :
    y ∈ trigVals (σ ++ [x]) ↔ (y ∈ trigVals σ ∨ (y = x ∧ ∃ z ∈ σ, z < x)) := by
  induction σ with
  | nil => simp [trigVals_cons]
  | cons a rest ih =>
    rw [List.cons_append, trigVals_cons, trigVals_cons, List.mem_append, List.mem_append,
      List.mem_filter, List.mem_filter, ih]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      decide_eq_true_eq]
    constructor
    · rintro (⟨hy | rfl, hay⟩ | h | ⟨rfl, z, hz, hzx⟩)
      · exact Or.inl (Or.inl ⟨hy, hay⟩)
      · exact Or.inr ⟨rfl, a, Or.inl rfl, hay⟩
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨rfl, z, Or.inr hz, hzx⟩
    · rintro ((⟨hy, hay⟩ | h) | ⟨rfl, z, rfl | hz, hzx⟩)
      · exact Or.inl ⟨Or.inl hy, hay⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inl ⟨Or.inr rfl, hzx⟩
      · exact Or.inr (Or.inr ⟨rfl, z, hz, hzx⟩)

/-! ### `2`-triggers by index

The separation predicate of \cref{cor:separators}(ii) names the trigger by its *value* and
compares positions with `List.idxOf`.  For a prefix with distinct letters the two spellings
agree; `isTrigger_two_iff` is the dictionary. -/

theorem getD_idxOf (ha : a ∈ σ) : σ.getD (σ.idxOf a) 0 = a := by
  have h := List.idxOf_lt_length_of_mem ha
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_idxOf h

theorem idxOf_getD (hnd : σ.Nodup) {i : ℕ} (hi : i < σ.length) : σ.idxOf (σ.getD i 0) = i := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.Nodup.idxOf_getElem hnd i hi

/-- **A `2`-trigger, by index.**  For a prefix with distinct letters, the letter `c` is a
`2`-trigger exactly when some smaller letter of `σ` occurs before it. -/
theorem isTriggerAt_two_idxOf_iff (hnd : σ.Nodup) (hc : c ∈ σ) :
    IsTriggerAt σ 2 (σ.idxOf c) ↔ ∃ a ∈ σ, σ.idxOf a < σ.idxOf c ∧ a < c := by
  rw [← trig2At_iff, Trig2At]
  constructor
  · rintro ⟨-, i, hi, hval⟩
    have hilt : i < σ.length := by
      have := List.idxOf_lt_length_of_mem hc; omega
    refine ⟨σ.getD i 0, ?_, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ hilt]; exact List.getElem_mem _
    · rw [idxOf_getD hnd hilt]; exact hi
    · rwa [getD_idxOf hc] at hval
  · rintro ⟨a, ha, hlt, hac⟩
    refine ⟨List.idxOf_lt_length_of_mem hc, σ.idxOf a, hlt, ?_⟩
    rw [getD_idxOf ha, getD_idxOf hc]
    exact hac

/-- **A `2`-trigger, by value.**  The form of \cref{cor:separators}(ii) used by the
separation predicate. -/
theorem isTrigger_two_iff (hnd : σ.Nodup) :
    IsTrigger σ 2 c ↔ (c ∈ σ ∧ ∃ a ∈ σ, σ.idxOf a < σ.idxOf c ∧ a < c) := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hjl := hj.lt_length
    have hmem : σ.getD j 0 ∈ σ := by
      rw [List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem _
    refine ⟨hmem, ?_⟩
    rw [← isTriggerAt_two_idxOf_iff hnd hmem, idxOf_getD hnd hjl]
    exact hj
  · rintro ⟨hc, h⟩
    exact ⟨σ.idxOf c, (isTriggerAt_two_idxOf_iff hnd hc).mpr h, getD_idxOf hc⟩

/-! ### The `foldl min` toolkit

`b1` and `b2` are both a `List.foldl min` over a list of candidate values with a virtual
default; these three lemmas are all that is needed about such a minimum. -/

private theorem foldl_min_cons (a d : ℕ) (t : List ℕ) :
    (a :: t).foldl min d = t.foldl min (min d a) := rfl

private theorem foldl_min_le : ∀ (l : List ℕ) (d : ℕ), l.foldl min d ≤ d := by
  intro l
  induction l with
  | nil => intro d; exact le_rfl
  | cons a t ih => intro d; exact (ih (min d a)).trans (min_le_left _ _)

private theorem foldl_min_le_of_mem : ∀ (l : List ℕ) (d : ℕ), y ∈ l → l.foldl min d ≤ y := by
  intro l
  induction l with
  | nil => intro d hy; simp at hy
  | cons a t ih =>
    intro d hy
    rcases List.mem_cons.mp hy with rfl | h
    · exact (foldl_min_le t (min d y)).trans (min_le_right _ _)
    · exact ih (min d a) h

private theorem foldl_min_mem_or_eq :
    ∀ (l : List ℕ) (d : ℕ), l.foldl min d ∈ l ∨ l.foldl min d = d := by
  intro l
  induction l with
  | nil => intro d; exact Or.inr rfl
  | cons a t ih =>
    intro d
    rw [foldl_min_cons]
    rcases ih (min d a) with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases min_cases d a with ⟨he, -⟩ | ⟨he, -⟩
      · exact Or.inr (h.trans he)
      · exact Or.inl (by rw [h, he]; simp)

/-! ### The two thresholds -/

/-- The first patience-sorting threshold `b₁`: the least letter of `σ`, with the virtual
value `n` for the empty prefix.  This is the one-threshold `m`. -/
def b1 (n : ℕ) (σ : List ℕ) : ℕ := OneThreshold.m n σ

/-- The second patience-sorting threshold `b₂`: the least value of a `2`-trigger of `σ`,
with the virtual value `n + 1` when `σ` has no `2`-trigger. -/
def b2 (n : ℕ) (σ : List ℕ) : ℕ := (trigVals σ).foldl min (n + 1)

theorem b1_eq_m (n : ℕ) (σ : List ℕ) : b1 n σ = OneThreshold.m n σ := rfl

@[simp] theorem b1_nil : b1 n [] = n := rfl

@[simp] theorem b2_nil : b2 n [] = n + 1 := rfl

theorem b1_le (n : ℕ) (σ : List ℕ) : b1 n σ ≤ n := OneThreshold.m_le n σ

theorem b1_le_of_mem (hy : y ∈ σ) : b1 n σ ≤ y := OneThreshold.m_le_of_mem hy

theorem b1_mem_or_eq : b1 n σ ∈ σ ∨ b1 n σ = n := OneThreshold.m_mem_or_eq

theorem b2_le_succ (n : ℕ) (σ : List ℕ) : b2 n σ ≤ n + 1 := foldl_min_le _ _

theorem b2_le_of_mem_trigVals (hy : y ∈ trigVals σ) : b2 n σ ≤ y :=
  foldl_min_le_of_mem _ _ hy

theorem b2_mem_or_eq : b2 n σ ∈ trigVals σ ∨ b2 n σ = n + 1 := foldl_min_mem_or_eq _ _

/-- The universal property of `b₂`: it is the greatest lower bound of the `2`-trigger values
and the virtual value `n + 1`. -/
theorem le_b2 {t : ℕ} (h1 : t ≤ n + 1) (h2 : ∀ z ∈ trigVals σ, t ≤ z) : t ≤ b2 n σ := by
  rcases b2_mem_or_eq (n := n) (σ := σ) with h | h
  · exact h2 _ h
  · rw [h]; exact h1

/-! ### \cref{lem:least-trigger-frontier} -/

/-- **\cref{lem:least-trigger-frontier}, lower bound.**  Every `2`-trigger value of the
prefix is at least `b₂`. -/
theorem b2_le_of_isTrigger {c : ℕ} (hc : IsTrigger σ 2 c) : b2 n σ ≤ c :=
  b2_le_of_mem_trigVals (mem_trigVals_iff.mpr hc)

/-- **\cref{lem:least-trigger-frontier}, lower bound**, by position. -/
theorem b2_le_of_isTriggerAt {j : ℕ} (hj : IsTriggerAt σ 2 j) : b2 n σ ≤ σ.getD j 0 :=
  b2_le_of_isTrigger ⟨j, hj, rfl⟩

/-- A nonvirtual `b₂` is a letter of the prefix. -/
theorem b2_mem_of_ne_virtual (h : b2 n σ ≠ n + 1) : b2 n σ ∈ σ :=
  mem_of_mem_trigVals (b2_mem_or_eq.resolve_right h)

/-- **\cref{lem:least-trigger-frontier}, attainment.**  A nonvirtual `b₂` is itself the value
of a `2`-trigger of the prefix. -/
theorem isTrigger_b2 (h : b2 n σ ≠ n + 1) : IsTrigger σ 2 (b2 n σ) :=
  mem_trigVals_iff.mp (b2_mem_or_eq.resolve_right h)

/-- **\cref{lem:least-trigger-frontier}, attainment**, by position. -/
theorem exists_isTriggerAt_b2 (h : b2 n σ ≠ n + 1) :
    ∃ j, IsTriggerAt σ 2 j ∧ σ.getD j 0 = b2 n σ := isTrigger_b2 h

/-- A nonvirtual `b₂` is below `n`, for a word. -/
theorem b2_lt_or_eq (hw : IsWord n σ) : b2 n σ < n ∨ b2 n σ = n + 1 := by
  rcases b2_mem_or_eq (n := n) (σ := σ) with h | h
  · exact Or.inl (hw.2 _ (mem_of_mem_trigVals h))
  · exact Or.inr h

/-- **`b₂ < n` detects the existence of a `2`-trigger.** -/
theorem b2_lt_iff_exists_trigger (hw : IsWord n σ) :
    b2 n σ < n ↔ ∃ j, IsTriggerAt σ 2 j := by
  constructor
  · intro h
    obtain ⟨j, hj, -⟩ := exists_isTriggerAt_b2 (n := n) (σ := σ) (by omega)
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    have h1 : b2 n σ ≤ σ.getD j 0 := b2_le_of_isTriggerAt hj
    have h2 : σ.getD j 0 ∈ σ := by
      rw [List.getD_eq_getElem _ _ hj.lt_length]; exact List.getElem_mem _
    exact lt_of_le_of_lt h1 (hw.2 _ h2)

/-- **The thresholds are ordered**: `b₁ < b₂`, in the virtual cases as well. -/
theorem b1_lt_b2 (n : ℕ) (σ : List ℕ) : b1 n σ < b2 n σ := by
  rcases b2_mem_or_eq (n := n) (σ := σ) with h | h
  · obtain ⟨j, ⟨hj, i, hij, hval⟩, hgy⟩ := mem_trigVals_iff_trig2At.mp h
    have hi : i < σ.length := by omega
    have hmem : σ.getD i 0 ∈ σ := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
    have := b1_le_of_mem (n := n) hmem
    omega
  · have := b1_le n σ
    omega

/-- `b₂` never increases along the scan. -/
theorem b2_succ_le (n : ℕ) (σ : List ℕ) (x : ℕ) : b2 n (σ ++ [x]) ≤ b2 n σ := by
  rcases b2_mem_or_eq (n := n) (σ := σ) with h | h
  · exact b2_le_of_mem_trigVals (mem_trigVals_append_singleton.mpr (Or.inl h))
  · rw [h]; exact b2_le_succ _ _

/-- `b₁` never increases along the scan. -/
theorem b1_succ_le (n : ℕ) (σ : List ℕ) (x : ℕ) : b1 n (σ ++ [x]) ≤ b1 n σ := by
  rw [b1, b1, OneThreshold.m_append_singleton]
  exact min_le_left _ _

/-- **\cref{lem:least-trigger-frontier} in the vocabulary of \cref{cor:separators}(ii)**: a
nonvirtual `b₂` has a smaller letter before it. -/
theorem exists_lt_before_b2 (hnd : σ.Nodup) (h : b2 n σ ≠ n + 1) :
    ∃ a ∈ σ, σ.idxOf a < σ.idxOf (b2 n σ) ∧ a < b2 n σ :=
  ((isTrigger_two_iff hnd).mp (isTrigger_b2 h)).2

/-- A nonvirtual `b₁` is a letter of the prefix. -/
theorem b1_mem_of_lt (h : b1 n σ < n) : b1 n σ ∈ σ :=
  b1_mem_or_eq.resolve_right (by omega)

/-- The first threshold has been read (or is out of range). -/
theorem b1_not_unread (n : ℕ) (σ : List ℕ) : b1 n σ ∉ unread n σ := by
  rw [mem_unread]
  rintro ⟨h1, h2⟩
  exact h2 (b1_mem_of_lt h1)

/-- The second threshold has been read (or is out of range). -/
theorem b2_not_unread (n : ℕ) (σ : List ℕ) : b2 n σ ∉ unread n σ := by
  rw [mem_unread]
  rintro ⟨h1, h2⟩
  exact h2 (b2_mem_of_ne_virtual (by omega))

/-- A last-band letter is a `2`-trigger of the extended prefix. -/
theorem isTrigger_succ_band1 (hx : x ∈ unread n σ) (h1 : b1 n σ < x) :
    IsTrigger (σ ++ [x]) 2 x := by
  rw [mem_unread] at hx
  exact mem_trigVals_iff.mp (mem_trigVals_append_singleton.mpr
    (Or.inr ⟨rfl, b1 n σ, b1_mem_of_lt (by omega), h1⟩))

/-! ### The bands and the control -/

/-- Band `0`: the unread values below `b₁`. -/
def B0 (n : ℕ) (σ : List ℕ) : Finset ℕ := (unread n σ).filter (fun y => y < b1 n σ)

/-- Band `1` (the last band at `d = 2`): the unread values strictly between `b₁` and `b₂`. -/
def B1 (n : ℕ) (σ : List ℕ) : Finset ℕ :=
  (unread n σ).filter (fun y => b1 n σ < y ∧ y < b2 n σ)

/-- The control `𝐩 = (p₀, p₁)`: the two band sizes. -/
def p (n : ℕ) (σ : List ℕ) : ℕ × ℕ := ((B0 n σ).card, (B1 n σ).card)

/-- The number of band-`0` values below `x`: the paper's `h` in \eqref{eq:T} at `i = 0`. -/
def below0 (n : ℕ) (σ : List ℕ) (x : ℕ) : ℕ := ((B0 n σ).filter (· < x)).card

/-- The number of band-`1` values below `x`: the paper's `h` in \eqref{eq:U} at `d = 2`. -/
def below1 (n : ℕ) (σ : List ℕ) (x : ℕ) : ℕ := ((B1 n σ).filter (· < x)).card

@[simp] theorem mem_B0 : y ∈ B0 n σ ↔ (y ∈ unread n σ ∧ y < b1 n σ) := by
  simp [B0]

@[simp] theorem mem_B1 : y ∈ B1 n σ ↔ (y ∈ unread n σ ∧ b1 n σ < y ∧ y < b2 n σ) := by
  simp [B1]

@[simp] theorem p_fst (n : ℕ) (σ : List ℕ) : (p n σ).1 = (B0 n σ).card := rfl

@[simp] theorem p_snd (n : ℕ) (σ : List ℕ) : (p n σ).2 = (B1 n σ).card := rfl

@[simp] theorem B0_nil (n : ℕ) : B0 n [] = Finset.range n := by
  ext y; simp [OneThreshold.unread]

@[simp] theorem B1_nil (n : ℕ) : B1 n [] = ∅ := by
  ext y; simp

/-- **The initial control** of \eqref{eq:initial-terminal} at `d = 2`: `𝐩 = (n, 0)`. -/
@[simp] theorem p_nil (n : ℕ) : p n [] = (n, 0) := by
  simp [p]

/-- **The three kinds of unread value.**  Every unread value lies in band `0`, in band `1`,
or strictly above `b₂`; the thresholds themselves are read. -/
theorem mem_B0_or_B1_or_gt_b2 (hx : x ∈ unread n σ) :
    x ∈ B0 n σ ∨ x ∈ B1 n σ ∨ b2 n σ < x := by
  have h1 : x ≠ b1 n σ := fun h => b1_not_unread n σ (h ▸ hx)
  have h2 : x ≠ b2 n σ := fun h => b2_not_unread n σ (h ▸ hx)
  rcases lt_trichotomy x (b1 n σ) with h | h | h
  · exact Or.inl (mem_B0.mpr ⟨hx, h⟩)
  · exact absurd h h1
  · rcases lt_trichotomy x (b2 n σ) with h' | h' | h'
    · exact Or.inr (Or.inl (mem_B1.mpr ⟨hx, h, h'⟩))
    · exact absurd h' h2
    · exact Or.inr (Or.inr h')

/-- The base values below `b₂` are exactly the two bands, so the control mass counts them. -/
theorem controlMass_eq (n : ℕ) (σ : List ℕ) :
    (p n σ).1 + (p n σ).2 = ((unread n σ).filter (fun y => y < b2 n σ)).card := by
  rw [p_fst, p_snd, ← Finset.card_union_of_disjoint, B0, B1]
  · refine congrArg _ (Finset.ext fun y => ?_)
    simp only [Finset.mem_union, Finset.mem_filter]
    have hlt := b1_lt_b2 n σ
    constructor
    · rintro (⟨hy, h⟩ | ⟨hy, -, h⟩) <;> exact ⟨hy, by omega⟩
    · rintro ⟨hy, h⟩
      rcases lt_trichotomy y (b1 n σ) with h' | h' | h'
      · exact Or.inl ⟨hy, h'⟩
      · exact absurd (h' ▸ hy) (b1_not_unread n σ)
      · exact Or.inr ⟨hy, h', h⟩
  · rw [Finset.disjoint_left]
    intro a ha hb
    simp only [B0, B1, Finset.mem_filter] at ha hb
    omega

/-! ### Reindexing a band by the in-band rank

`Av12453.OneThreshold.sum_rank_eq` applied to `B0` and `B1`: summing over the band and
summing over `h = 0, …, p_i - 1` are the same, which is how \eqref{eq:T} and \eqref{eq:U}
turn a sum over letters into a sum over `h`. -/

theorem sum_below0_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ x ∈ B0 n σ, f (below0 n σ x) = ∑ h ∈ Finset.range (p n σ).1, f h :=
  sum_rank_eq (B0 n σ) f

theorem sum_below1_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ x ∈ B1 n σ, f (below1 n σ x) = ∑ h ∈ Finset.range (p n σ).2, f h :=
  sum_rank_eq (B1 n σ) f

/-! ### Two dictionary lemmas for the stack -/

/-- The values a last-band letter adjoins to the active head -- the paper's `E` of
\eqref{eq:U}, the unread values strictly between `x` and the old `b₂` -- are exactly the
band-`1` values above `x`.  With `card_band1_gt` this gives `|E| = δ_h = p₁ - 1 - h`. -/
theorem filter_between_eq_band1_gt (hx : x ∈ B1 n σ) :
    (unread n σ).filter (fun y => x < y ∧ y < b2 n σ) = (B1 n σ).filter (fun y => x < y) := by
  rw [mem_B1] at hx
  ext y
  simp only [Finset.mem_filter, mem_B1]
  constructor
  · rintro ⟨hy, h1, h2⟩; exact ⟨⟨hy, by omega, h2⟩, h1⟩
  · rintro ⟨⟨hy, -, h2⟩, h1⟩; exact ⟨hy, h1, h2⟩

/-- For a band-`0` letter the in-band rank is the global count of unread values below it,
i.e. the `below` of the one-threshold development. -/
theorem below0_eq_below (hx : x ∈ B0 n σ) : below0 n σ x = OneThreshold.below n σ x := by
  rw [mem_B0] at hx
  rw [below0, OneThreshold.below]
  refine congrArg _ (Finset.ext fun y => ?_)
  simp only [Finset.mem_filter, mem_B0]
  constructor
  · rintro ⟨⟨hy, -⟩, h⟩; exact ⟨hy, h⟩
  · rintro ⟨hy, h⟩; exact ⟨⟨hy, by omega⟩, h⟩

/-! ### The threshold transitions

The three cases of \cref{sec:frontier}: an early-band letter `x < b₁` replaces `b₁`, a
last-band letter `b₁ < x < b₂` replaces `b₂` (it is the new least `2`-trigger), and a letter
`x > b₂` replaces neither. -/

theorem b1_succ_band0 (hlt : x < b1 n σ) : b1 n (σ ++ [x]) = x :=
  OneThreshold.m_succ_newMin hlt

theorem b1_succ_of_le (hge : b1 n σ ≤ x) : b1 n (σ ++ [x]) = b1 n σ :=
  OneThreshold.m_succ_active hge

/-- An early-band letter is smaller than every letter read so far, so it creates no
`2`-trigger. -/
theorem b2_succ_band0 (hlt : x < b1 n σ) : b2 n (σ ++ [x]) = b2 n σ := by
  have hno : ¬ ∃ z ∈ σ, z < x := by
    rintro ⟨z, hz, hzx⟩
    have := b1_le_of_mem (n := n) hz
    omega
  have hsame : ∀ z, z ∈ trigVals (σ ++ [x]) ↔ z ∈ trigVals σ := by
    intro z
    rw [mem_trigVals_append_singleton]
    constructor
    · rintro (h | ⟨-, h⟩)
      · exact h
      · exact absurd h hno
    · exact Or.inl
  refine le_antisymm (le_b2 (b2_le_succ n (σ ++ [x])) ?_) (le_b2 (b2_le_succ n σ) ?_)
  · intro z hz
    exact b2_le_of_mem_trigVals ((hsame z).mpr hz)
  · intro z hz
    exact b2_le_of_mem_trigVals ((hsame z).mp hz)

/-- A last-band letter is the new least `2`-trigger. -/
theorem b2_succ_band1 (hx : x ∈ unread n σ) (h1 : b1 n σ < x) (h2 : x < b2 n σ) :
    b2 n (σ ++ [x]) = x := by
  rw [mem_unread] at hx
  have hb1 : b1 n σ ∈ σ := b1_mem_of_lt (by omega)
  have hmem : x ∈ trigVals (σ ++ [x]) :=
    mem_trigVals_append_singleton.mpr (Or.inr ⟨rfl, b1 n σ, hb1, h1⟩)
  refine le_antisymm (b2_le_of_mem_trigVals hmem) (le_b2 (by omega) ?_)
  intro z hz
  rcases mem_trigVals_append_singleton.mp hz with h | ⟨rfl, -⟩
  · have := b2_le_of_mem_trigVals (n := n) h
    omega
  · exact le_rfl

/-- A letter above `b₂` is a `2`-trigger, but not a smaller one. -/
theorem b2_succ_above (hx : x ∈ unread n σ) (h : b2 n σ < x) : b2 n (σ ++ [x]) = b2 n σ := by
  rw [mem_unread] at hx
  have hne : b2 n σ ≠ n + 1 := by omega
  have hmem : b2 n σ ∈ trigVals σ := b2_mem_or_eq.resolve_right hne
  refine le_antisymm (b2_le_of_mem_trigVals
    (mem_trigVals_append_singleton.mpr (Or.inl hmem))) (le_b2 (by omega) ?_)
  intro z hz
  rcases mem_trigVals_append_singleton.mp hz with hz' | ⟨rfl, -⟩
  · exact b2_le_of_mem_trigVals hz'
  · omega

/-- **Early-band threshold transition** (\cref{sec:frontier}): `x < b₁` becomes the new
`b₁`, and `b₂` is unchanged. -/
theorem thresholds_succ_band0 (hlt : x < b1 n σ) :
    b1 n (σ ++ [x]) = x ∧ b2 n (σ ++ [x]) = b2 n σ :=
  ⟨b1_succ_band0 hlt, b2_succ_band0 hlt⟩

/-- **Last-band threshold transition** (\cref{sec:frontier}): `b₁ < x < b₂` becomes the new
`b₂`, and `b₁` is unchanged. -/
theorem thresholds_succ_band1 (hx : x ∈ unread n σ) (h1 : b1 n σ < x) (h2 : x < b2 n σ) :
    b1 n (σ ++ [x]) = b1 n σ ∧ b2 n (σ ++ [x]) = x :=
  ⟨b1_succ_of_le (by omega), b2_succ_band1 hx h1 h2⟩

/-- **Active-interval threshold transition** (\cref{sec:frontier}): a letter above `b₂`
changes neither threshold. -/
theorem thresholds_succ_above (hx : x ∈ unread n σ) (h : b2 n σ < x) :
    b1 n (σ ++ [x]) = b1 n σ ∧ b2 n (σ ++ [x]) = b2 n σ :=
  ⟨b1_succ_of_le (by have := b1_lt_b2 n σ; omega), b2_succ_above hx h⟩

/-! ### The band transitions

\eqref{eq:T} at `i = 0`, \eqref{eq:U} at `d = 2`, and the invariance of the control under an
active-interval move. -/

theorem B0_succ_band0 (hx : x ∈ B0 n σ) : B0 n (σ ++ [x]) = (B0 n σ).filter (· < x) := by
  rw [mem_B0] at hx
  ext y
  simp only [mem_B0, Finset.mem_filter, unread_append_singleton, Finset.mem_erase,
    b1_succ_band0 hx.2]
  constructor
  · rintro ⟨⟨-, hy⟩, hyx⟩; exact ⟨⟨hy, by omega⟩, hyx⟩
  · rintro ⟨⟨hy, -⟩, hyx⟩; exact ⟨⟨by omega, hy⟩, hyx⟩

theorem B1_succ_band0 (hx : x ∈ B0 n σ) :
    B1 n (σ ++ [x]) = (B0 n σ).filter (fun y => x < y) ∪ B1 n σ := by
  rw [mem_B0] at hx
  have hlt := b1_lt_b2 n σ
  ext y
  simp only [mem_B1, mem_B0, Finset.mem_union, Finset.mem_filter, unread_append_singleton,
    Finset.mem_erase, b1_succ_band0 hx.2, b2_succ_band0 hx.2]
  constructor
  · rintro ⟨⟨hne, hy⟩, hxy, hyb2⟩
    rcases lt_trichotomy y (b1 n σ) with h | h | h
    · exact Or.inl ⟨⟨hy, h⟩, hxy⟩
    · exact absurd (h ▸ hy) (b1_not_unread n σ)
    · exact Or.inr ⟨hy, h, hyb2⟩
  · rintro (⟨⟨hy, hyb1⟩, hxy⟩ | ⟨hy, hb1y, hyb2⟩)
    · exact ⟨⟨by omega, hy⟩, hxy, by omega⟩
    · exact ⟨⟨by omega, hy⟩, by omega, hyb2⟩

/-- **The early-band control transition**, \eqref{eq:T} at `i = 0`: reading a band-`0` value
with `h` band-`0` values below it gives the control `(h, p₁ + p₀ - 1 - h)`. -/
theorem p_succ_band0 (hx : x ∈ B0 n σ) :
    p n (σ ++ [x]) =
      (below0 n σ x, (p n σ).2 + (p n σ).1 - 1 - below0 n σ x) := by
  have hcard := card_filter_lt_add_card_filter_gt hx
  have hdisj : Disjoint ((B0 n σ).filter (fun y => x < y)) (B1 n σ) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_filter, mem_B0, mem_B1] at ha hb
    omega
  refine Prod.ext ?_ ?_
  · rw [p_fst, B0_succ_band0 hx]; rfl
  · rw [p_snd, B1_succ_band0 hx, Finset.card_union_of_disjoint hdisj, p_fst, p_snd, below0]
    omega

theorem B0_succ_band1 (hx : x ∈ B1 n σ) : B0 n (σ ++ [x]) = B0 n σ := by
  rw [mem_B1] at hx
  ext y
  simp only [mem_B0, unread_append_singleton, Finset.mem_erase,
    b1_succ_of_le (le_of_lt hx.2.1)]
  constructor
  · rintro ⟨⟨-, hy⟩, h⟩; exact ⟨hy, h⟩
  · rintro ⟨hy, h⟩; exact ⟨⟨by omega, hy⟩, h⟩

theorem B1_succ_band1 (hx : x ∈ B1 n σ) :
    B1 n (σ ++ [x]) = (B1 n σ).filter (· < x) := by
  have hx' := mem_B1.mp hx
  ext y
  simp only [mem_B1, Finset.mem_filter, unread_append_singleton, Finset.mem_erase,
    b1_succ_of_le (le_of_lt hx'.2.1), b2_succ_band1 hx'.1 hx'.2.1 hx'.2.2]
  constructor
  · rintro ⟨⟨-, hy⟩, h1, h2⟩; exact ⟨⟨hy, h1, by omega⟩, h2⟩
  · rintro ⟨⟨hy, h1, -⟩, h2⟩; exact ⟨⟨by omega, hy⟩, h1, h2⟩

/-- **The last-band control transition**, \eqref{eq:U} at `d = 2`: reading a band-`1` value
with `h` band-`1` values below it gives the control `(p₀, h)`. -/
theorem p_succ_band1 (hx : x ∈ B1 n σ) :
    p n (σ ++ [x]) = ((p n σ).1, below1 n σ x) := by
  refine Prod.ext ?_ ?_
  · rw [p_fst, B0_succ_band1 hx]; rfl
  · rw [p_snd, B1_succ_band1 hx]; rfl

/-- The number of unread band-`1` values above a band-`1` letter: the paper's
`δ_h = p₁ - 1 - h` of \eqref{eq:U}. -/
theorem card_band1_gt (hx : x ∈ B1 n σ) :
    ((B1 n σ).filter (fun y => x < y)).card = (p n σ).2 - 1 - below1 n σ x := by
  have hcard := card_filter_lt_add_card_filter_gt hx
  rw [p_snd, below1]
  omega

theorem B0_succ_above (h : b2 n σ < x) : B0 n (σ ++ [x]) = B0 n σ := by
  have hlt := b1_lt_b2 n σ
  ext y
  simp only [mem_B0, unread_append_singleton, Finset.mem_erase,
    b1_succ_of_le (show b1 n σ ≤ x by omega)]
  constructor
  · rintro ⟨⟨-, hy⟩, h'⟩; exact ⟨hy, h'⟩
  · rintro ⟨hy, h'⟩; exact ⟨⟨by omega, hy⟩, h'⟩

theorem B1_succ_above (hx : x ∈ unread n σ) (h : b2 n σ < x) : B1 n (σ ++ [x]) = B1 n σ := by
  have hlt := b1_lt_b2 n σ
  ext y
  simp only [mem_B1, unread_append_singleton, Finset.mem_erase,
    b1_succ_of_le (show b1 n σ ≤ x by omega), b2_succ_above hx h]
  constructor
  · rintro ⟨⟨-, hy⟩, h1, h2⟩; exact ⟨hy, h1, h2⟩
  · rintro ⟨hy, h1, h2⟩; exact ⟨⟨by omega, hy⟩, h1, h2⟩

/-- **The active-interval control transition**: a letter above `b₂` leaves the control
unchanged. -/
theorem p_succ_above (hx : x ∈ unread n σ) (h : b2 n σ < x) : p n (σ ++ [x]) = p n σ := by
  rw [p, p, B0_succ_above h, B1_succ_above hx h]

/-! ### Sanity checks

The running example of \eqref{eq:running-example}, `π = 9,11,10,14,5,12,6,2,3,8,4,7,1,13,15`,
written `0`-based, and the columns `b₁, b₂`, `B₀`, `B₁` and `𝐩` of \cref{ex:full-state}.
Every check is a kernel evaluation (`decide`), so none of them adds an axiom.  Row `i` of the
paper's table is the prefix of length `i` here, and row `0` is the empty prefix, whose
thresholds are both virtual. -/

/-- The paper's running example \eqref{eq:running-example}, `0`-based. -/
def runningExample : List ℕ := [8, 10, 9, 13, 4, 11, 5, 1, 2, 7, 3, 6, 0, 12, 14]

set_option maxRecDepth 100000 in
/-- The `b₁, b₂` column of \cref{ex:full-state}, `0`-based, with the virtual values `15`
and `16`. -/
example : (List.range 16).map (fun k => (b1 15 (runningExample.take k),
    b2 15 (runningExample.take k))) =
    [(15, 16), (8, 16), (8, 10), (8, 9), (8, 9), (4, 9), (4, 9), (4, 5), (1, 5), (1, 2),
      (1, 2), (1, 2), (1, 2), (0, 2), (0, 2), (0, 2)] := by decide

set_option maxRecDepth 100000 in
/-- The `B₀` column of \cref{ex:full-state}, `0`-based. -/
example : (List.range 16).map (fun k => B0 15 (runningExample.take k)) =
    [{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14}, {0, 1, 2, 3, 4, 5, 6, 7},
      {0, 1, 2, 3, 4, 5, 6, 7}, {0, 1, 2, 3, 4, 5, 6, 7}, {0, 1, 2, 3, 4, 5, 6, 7},
      {0, 1, 2, 3}, {0, 1, 2, 3}, {0, 1, 2, 3}, {0}, {0}, {0}, {0}, {0}, ∅, ∅, ∅] := by
  decide

set_option maxRecDepth 100000 in
/-- The `B₁` column of \cref{ex:full-state}, `0`-based. -/
example : (List.range 16).map (fun k => B1 15 (runningExample.take k)) =
    [∅, {9, 10, 11, 12, 13, 14}, {9}, ∅, ∅, {5, 6, 7}, {5, 6, 7}, ∅, {2, 3}, ∅, ∅, ∅, ∅,
      ∅, ∅, ∅] := by decide

set_option maxRecDepth 100000 in
/-- The control column of \cref{ex:full-state}: `𝐩` after each prefix. -/
example : (List.range 16).map (fun k => p 15 (runningExample.take k)) =
    [(15, 0), (8, 6), (8, 1), (8, 0), (8, 0), (4, 3), (4, 3), (4, 0), (1, 2), (1, 0),
      (1, 0), (1, 0), (1, 0), (0, 0), (0, 0), (0, 0)] := by decide

set_option maxRecDepth 100000 in
/-- **\cref{lem:least-trigger-frontier} on the running example.**  After six letters the
`2`-trigger values are the paper's `10, 11, 12, 14` (`0`-based `9, 10, 11, 13`), and `b₂` is
the least of them.  This runs the `IsTrigger _ 2 _` decision procedure in the kernel. -/
example : ((List.range 15).filter (fun c => decide (IsTrigger (runningExample.take 6) 2 c)),
    b2 15 (runningExample.take 6)) = ([9, 10, 11, 13], 9) := by decide

set_option maxRecDepth 100000 in
/-- After one letter there is no `2`-trigger, so `b₂` is virtual (row `1` of
\cref{ex:full-state}, where the paper writes a dot). -/
example : ((List.range 15).filter (fun c => decide (IsTrigger (runningExample.take 1) 2 c)),
    b2 15 (runningExample.take 1)) = ([], 16) := by decide

end TwoThreshold
end Av12453
