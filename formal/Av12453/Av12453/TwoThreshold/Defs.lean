/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Av12453.TwoThreshold.Thresholds
import Av12453.OneThreshold.Semantics

/-!
# The two-threshold scan and the literal recurrence for `Av(12453)`

This file sets up the objects of \cref{sec:frontier} and \cref{sec:literal} of the paper
*Protected tails and polynomial-time enumeration of permutations avoiding a direct sum of an
increasing pattern and 231* at `d = 2`, where
`β₂ = ι₂ ⊕ 231 = 12453` (`0`-based `[0, 1, 3, 4, 2]`, `Av12453.beta_two`).  Values and
positions are `0`-based throughout, as in `Av12453.Basic`.

The patience thresholds `b₁ < b₂`, the bands `B₀`, `B₁` and the control
`𝐩 = (p₀, p₁)` are supplied by `Av12453.TwoThreshold.Thresholds`; this file adds the
interval stack, the layout invariant, the separation vocabulary, the recurrence `H` and the
prefix-counting function `A`.

## The scan

A *prefix* is a list `σ : List ℕ` of letters read so far.  `step` performs one move on the
interval stack.  With `x` the next letter and the thresholds `b₁ < b₂` of `σ`:

* `x < b₁` (an **early-band** move, \eqref{eq:T} at `i = 0`): `x` becomes the new `b₁`, the
  old band-`0` values above `x` join band `1`, and the stack is unchanged.  This case has no
  analogue for `d = 1`.
* `b₁ < x < b₂` (a **last-band** move, \eqref{eq:U}): `x` is the new least `2`-trigger and
  becomes `b₂`; the unread values strictly between `x` and the old `b₂` -- the paper's `E`,
  here `mergeSet n σ x` -- join the active head (\cref{lem:merger}), or become the whole
  stack when the stack was empty.
* `x > b₂` and `x ∈ I₁` (an **active-interval** move): `x` splits the active head into its
  lower and upper parts (\cref{lem:first-letter}), thresholds unchanged.
* `x > b₂` in a deferred interval `I_j`, `j ≥ 2`: illegal, `none`.

`stackOf`/`stack` iterate `step` along the prefix, `Legal n σ` says that every move was
legal, and `L n σ` lists the interval sizes.

## The recurrence

`H 𝐩 L` is \eqref{eq:H} at `d = 2` with \eqref{eq:initial-terminal}, defined by recursion on
the measure `ρ(𝐩, L) = p₀ + p₁ + L.sum` of \eqref{eq:rho} (`rho_eq`) and characterized by
`H_eq_nil`, `H_eq_cons` and `H_endpoint`.

## Main definitions

* `mergeSet`, `step`, `stackAux`, `stackOf`, `Legal`, `stack`, `L` : the interval stack.
* `Layout` : the ordered-layout invariant \eqref{eq:ordered-layout} at `d = 2`.
* `Sep`, `DiffIntervals` : the vocabulary of \cref{cor:separators} (ii) and (i);
  `Adjacent` is reused from the one-threshold development.
* `H`, `Eend` : the two-threshold literal recurrence.
* `A` : the number of `12453`-avoiders with a given prefix.

## Main results

* `layout_of_legal` : every legal prefix has the ordered layout.
* `H_eq_nil`, `H_eq_cons`, `H_endpoint`, `H_zero` : the defining equations of `H`.
* `A_succ`, `A_complete` : the prefix partition of the avoiders.
* `pL_succ_band0`, `pL_succ_band1_cons`, `pL_succ_band1_nil`, `pL_succ_active` : the effect
  of one move on `(𝐩, L)`, i.e. the four groups of \eqref{eq:H}.
* `legal_succ_iff_cons`, `legal_succ_iff_nil` : which letters are legal.
* `card_unread_succ`, `rho_eq` : the measure \eqref{eq:rho}.
* `sum_unread_split`, `below0_lt`, `below1_lt` : regrouping the next letter into the three
  groups of \eqref{eq:H}.
* `SepInvariant`, `DeferredHyp`, `CompleteHyp` : theorems (A), (B) and (C) of component 3b
  as hypotheses, so that (B), (C) and (D) can be proved independently of each other.
-/

namespace Av12453
namespace TwoThreshold

open OneThreshold (unread mem_unread unread_append_singleton IsWord nzI mem_nzI nzI_sublist
  nz nz_nil nz_singleton nz_singleton_sum map_card_nzI stackUnion mem_stackUnion
  stackUnion_cons stackUnion_append stackUnion_nzI card_stackUnion Adjacent perms mem_perms
  avoiders sum_rank_eq card_filter_lt_add_card_filter_gt rank_lt_card rank_inj card_unread
  isPermOf_of_isWord prefix_append_singleton_iff getD_mem_unread
  exists_adjacent_above exists_adjacent_around)

variable {n : ℕ} {σ τ : List ℕ} {x u v : ℕ}

/-! ### Deleting zero entries

Three small lemmas about `Av12453.OneThreshold.nz`, the paper's `\nz`, that the two-band
transitions need. -/

theorem nz_cons_zero (l : List ℕ) : nz (0 :: l) = nz l := by
  simp [OneThreshold.nz]

theorem nz_cons_of_ne_zero {a : ℕ} (ha : a ≠ 0) (l : List ℕ) : nz (a :: l) = a :: nz l := by
  simp [OneThreshold.nz, ha]

theorem nz_eq_self {l : List ℕ} (h : ∀ a ∈ l, a ≠ 0) : nz l = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [nz_cons_of_ne_zero (h a List.mem_cons_self) t,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

@[simp] theorem nz_sum (l : List ℕ) : (nz l).sum = l.sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rcases eq_or_ne a 0 with rfl | ha
    · rw [nz_cons_zero, ih, List.sum_cons, Nat.zero_add]
    · rw [nz_cons_of_ne_zero ha, List.sum_cons, List.sum_cons, ih]

/-! ### The interval stack -/

/--
The values a last-band letter adjoins to the active head: the paper's `E` of
\eqref{eq:U}, the unread values strictly between `x` and the old `b₂`.  Its size is the
paper's `δ_h = p₁ - 1 - h` (`card_mergeSet`).
-/
def mergeSet (n : ℕ) (σ : List ℕ) (x : ℕ) : Finset ℕ :=
  (unread n σ).filter (fun y => x < y ∧ y < b2 n σ)

theorem mem_mergeSet {y : ℕ} :
    y ∈ mergeSet n σ x ↔ (y ∈ unread n σ ∧ x < y ∧ y < b2 n σ) := by
  simp only [mergeSet, Finset.mem_filter]

/-- `mergeSet` is the set of band-`1` values above `x`. -/
theorem mergeSet_eq_band1_gt (hx : x ∈ B1 n σ) :
    mergeSet n σ x = (B1 n σ).filter (fun y => x < y) :=
  filter_between_eq_band1_gt hx

/--
One move of the two-threshold scan.  `σ` is the prefix read so far, `st` its interval stack,
and `x` the next letter; `none` marks an illegal move.  The four cases are the three kinds
of legal move classified by \cref{prop:state-invariant}(b) at `d = 2` -- a non-trigger
(early-band) move, a merger (last-band) move and a split (active-interval) move, in the
vocabulary of \cref{def:scan-state} -- together with the illegal letters of a deferred
interval.
-/
def step (n : ℕ) (σ : List ℕ) (st : List (Finset ℕ)) (x : ℕ) : Option (List (Finset ℕ)) :=
  if x ∈ unread n σ then
    if x < b1 n σ then some st
    else if x < b2 n σ then
      match st with
      | I₁ :: tail => some ((mergeSet n σ x ∪ I₁) :: tail)
      | [] => some (nzI [mergeSet n σ x])
    else
      match st with
      | I₁ :: tail =>
          if x ∈ I₁ then
            some (nzI [I₁.filter (· < x), I₁.filter (fun y => x < y)] ++ tail)
          else none
      | [] => none
  else none

theorem step_of_not_unread {st : List (Finset ℕ)} (hx : x ∉ unread n σ) :
    step n σ st x = none := by
  simp [step, hx]

/-- **Early-band move**: the stack does not change. -/
theorem step_band0 {st : List (Finset ℕ)} (hx : x ∈ B0 n σ) : step n σ st x = some st := by
  rw [mem_B0] at hx
  simp [step, hx.1, hx.2]

/-- **Last-band move** at a nonempty stack: `E` joins the active head. -/
theorem step_band1_cons {I₁ : Finset ℕ} {tail : List (Finset ℕ)} (hx : x ∈ B1 n σ) :
    step n σ (I₁ :: tail) x = some ((mergeSet n σ x ∪ I₁) :: tail) := by
  rw [mem_B1] at hx
  simp [step, hx.1, Nat.not_lt.mpr (le_of_lt hx.2.1), hx.2.2]

/-- **Last-band move** at an empty stack: `E` becomes the whole stack. -/
theorem step_band1_nil (hx : x ∈ B1 n σ) :
    step n σ [] x = some (nzI [mergeSet n σ x]) := by
  rw [mem_B1] at hx
  simp [step, hx.1, Nat.not_lt.mpr (le_of_lt hx.2.1), hx.2.2]

/-- **Active-interval move**: `x` splits the active head. -/
theorem step_active {I₁ : Finset ℕ} {tail : List (Finset ℕ)} (hx : x ∈ unread n σ)
    (hgt : b2 n σ < x) (hmem : x ∈ I₁) :
    step n σ (I₁ :: tail) x =
      some (nzI [I₁.filter (· < x), I₁.filter (fun y => x < y)] ++ tail) := by
  have hb := b1_lt_b2 n σ
  simp [step, hx, Nat.not_lt.mpr (le_of_lt (lt_trans hb hgt)), Nat.not_lt.mpr (le_of_lt hgt),
    hmem]

/-- **Deferred move**: a value above `b₂` outside the active head is illegal. -/
theorem step_deferred {I₁ : Finset ℕ} {tail : List (Finset ℕ)} (hgt : b2 n σ < x)
    (hmem : x ∉ I₁) : step n σ (I₁ :: tail) x = none := by
  have hb := b1_lt_b2 n σ
  by_cases hx : x ∈ unread n σ <;>
    simp [step, hx, Nat.not_lt.mpr (le_of_lt (lt_trans hb hgt)),
      Nat.not_lt.mpr (le_of_lt hgt), hmem]

/-- **Deferred move at an empty stack**: no letter above `b₂` is legal. -/
theorem step_nil_above (hgt : b2 n σ < x) : step n σ [] x = none := by
  have hb := b1_lt_b2 n σ
  by_cases hx : x ∈ unread n σ <;>
    simp [step, hx, Nat.not_lt.mpr (le_of_lt (lt_trans hb hgt)), Nat.not_lt.mpr (le_of_lt hgt)]

theorem unread_of_step_isSome {st : List (Finset ℕ)} (h : (step n σ st x).isSome) :
    x ∈ unread n σ := by
  by_contra hx
  rw [step_of_not_unread hx] at h
  exact Bool.noConfusion h

/-- Scanning the letters of a word one at a time, starting from the prefix `τ` with stack
`st`. -/
def stackAux (n : ℕ) : List ℕ → List (Finset ℕ) → List ℕ → Option (List (Finset ℕ))
  | _, st, [] => some st
  | τ, st, y :: rest => (step n τ st y).bind fun st' => stackAux n (τ ++ [y]) st' rest

/-- The interval stack of the prefix `σ`; `none` when some move of the scan was illegal. -/
def stackOf (n : ℕ) (σ : List ℕ) : Option (List (Finset ℕ)) := stackAux n [] [] σ

@[simp] theorem stackOf_nil : stackOf n [] = some [] := rfl

theorem stackAux_append_singleton (n : ℕ) (ys : List ℕ) :
    ∀ (τ : List ℕ) (st : List (Finset ℕ)) (y : ℕ),
      stackAux n τ st (ys ++ [y]) =
        (stackAux n τ st ys).bind fun st' => step n (τ ++ ys) st' y := by
  induction ys with
  | nil => intro τ st y; simp [stackAux]
  | cons z zs ih =>
    intro τ st y
    simp only [List.cons_append, stackAux]
    cases hstep : step n τ st z with
    | none => simp
    | some st' => simp [ih, List.append_assoc]

/-- The scan of `σ ++ [x]` is the scan of `σ` followed by one step. -/
theorem stackOf_append_singleton :
    stackOf n (σ ++ [x]) = (stackOf n σ).bind fun st => step n σ st x := by
  have h := stackAux_append_singleton n σ [] [] x
  rw [List.nil_append] at h
  exact h

/-- `σ` is *legal*: every move of the scan was a legal move. -/
def Legal (n : ℕ) (σ : List ℕ) : Prop := (stackOf n σ).isSome

instance : DecidablePred (Legal n) := fun _ => inferInstanceAs (Decidable (_ = true))

/-- The interval stack of a legal prefix. -/
def stack (n : ℕ) (σ : List ℕ) : List (Finset ℕ) := (stackOf n σ).getD []

/-- The list of interval sizes: the paper's `L = (ℓ₁, …, ℓ_s)`. -/
def L (n : ℕ) (σ : List ℕ) : List ℕ := (stack n σ).map Finset.card

@[simp] theorem stack_nil : stack n [] = [] := rfl

@[simp] theorem L_nil : L n [] = [] := rfl

@[simp] theorem Legal_nil : Legal n [] := rfl

theorem stackOf_eq_some (h : Legal n σ) : stackOf n σ = some (stack n σ) := by
  rw [stack]
  cases hs : stackOf n σ with
  | none => rw [Legal, hs] at h; exact Bool.noConfusion h
  | some st => rfl

/-- On a legal prefix, one more letter is scanned by a single `step`. -/
theorem stackOf_succ (h : Legal n σ) : stackOf n (σ ++ [x]) = step n σ (stack n σ) x := by
  rw [stackOf_append_singleton, stackOf_eq_some h, Option.bind_some]

theorem stack_succ (h : Legal n σ) (h' : Legal n (σ ++ [x])) :
    step n σ (stack n σ) x = some (stack n (σ ++ [x])) := by
  rw [← stackOf_succ h, stackOf_eq_some h']

/-! ### Legality is prefix-closed -/

theorem Legal.of_append_singleton (h : Legal n (σ ++ [x])) : Legal n σ := by
  rw [Legal, stackOf_append_singleton] at h
  cases hs : stackOf n σ with
  | none => rw [hs] at h; exact absurd h (by simp)
  | some st => rw [Legal, hs]; rfl

theorem Legal.prefix (hσ : σ <+: τ) (h : Legal n τ) : Legal n σ := by
  induction τ using List.reverseRecOn with
  | nil => rw [List.prefix_nil.mp hσ]; exact Legal_nil
  | append_singleton t y ih =>
    rcases Nat.lt_or_ge σ.length (t ++ [y]).length with hlen | hlen
    · refine ih (List.prefix_of_prefix_length_le hσ (List.prefix_append t [y]) ?_)
        h.of_append_singleton
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    · have : σ = t ++ [y] := hσ.eq_of_length (le_antisymm hσ.length_le hlen)
      rw [this]; exact h

theorem Legal.mem_unread (h : Legal n (σ ++ [x])) : x ∈ unread n σ :=
  unread_of_step_isSome (st := stack n σ)
    (by rw [stack_succ h.of_append_singleton h]; rfl)

/-- Every letter of a legal prefix is an unread value at the moment it is read. -/
theorem Legal.isWord (h : Legal n σ) : IsWord n σ := by
  induction σ using List.reverseRecOn with
  | nil => exact ⟨List.nodup_nil, by simp⟩
  | append_singleton t y ih =>
    have ht := h.of_append_singleton
    obtain ⟨hnd, hlt⟩ := ih ht
    have hy : y ∈ unread n t := h.mem_unread
    rw [OneThreshold.mem_unread] at hy
    refine ⟨?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hnd, List.nodup_singleton y, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton.mp hb]
      exact fun hc => hy.2 (hc ▸ ha)
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hlt z hz
      · rw [List.mem_singleton.mp hz]; exact hy.1

theorem Legal.nodup (h : Legal n σ) : σ.Nodup := h.isWord.1

/-! ### Legal successors -/

/-- **Early-band successor**: the stack is unchanged. -/
theorem legal_succ_of_band0 (hleg : Legal n σ) (hx : x ∈ B0 n σ) :
    Legal n (σ ++ [x]) ∧ stack n (σ ++ [x]) = stack n σ := by
  have h : stackOf n (σ ++ [x]) = some (stack n σ) := by
    rw [stackOf_succ hleg, step_band0 hx]
  exact ⟨by rw [Legal, h]; rfl, by rw [stack, h]; rfl⟩

/-- **Last-band successor** at a nonempty stack. -/
theorem legal_succ_of_band1_cons (hleg : Legal n σ) {I₁ : Finset ℕ} {tail : List (Finset ℕ)}
    (hst : stack n σ = I₁ :: tail) (hx : x ∈ B1 n σ) :
    Legal n (σ ++ [x]) ∧ stack n (σ ++ [x]) = (mergeSet n σ x ∪ I₁) :: tail := by
  have h : stackOf n (σ ++ [x]) = some ((mergeSet n σ x ∪ I₁) :: tail) := by
    rw [stackOf_succ hleg, hst, step_band1_cons hx]
  exact ⟨by rw [Legal, h]; rfl, by rw [stack, h]; rfl⟩

/-- **Last-band successor** at an empty stack. -/
theorem legal_succ_of_band1_nil (hleg : Legal n σ) (hst : stack n σ = [])
    (hx : x ∈ B1 n σ) :
    Legal n (σ ++ [x]) ∧ stack n (σ ++ [x]) = nzI [mergeSet n σ x] := by
  have h : stackOf n (σ ++ [x]) = some (nzI [mergeSet n σ x]) := by
    rw [stackOf_succ hleg, hst, step_band1_nil hx]
  exact ⟨by rw [Legal, h]; rfl, by rw [stack, h]; rfl⟩

/-- **Active-interval successor**: the head splits. -/
theorem legal_succ_of_active (hleg : Legal n σ) {I₁ : Finset ℕ} {tail : List (Finset ℕ)}
    (hst : stack n σ = I₁ :: tail) (hx : x ∈ unread n σ) (hgt : b2 n σ < x) (hmem : x ∈ I₁) :
    Legal n (σ ++ [x]) ∧
      stack n (σ ++ [x]) = nzI [I₁.filter (· < x), I₁.filter fun y => x < y] ++ tail := by
  have h : stackOf n (σ ++ [x]) =
      some (nzI [I₁.filter (· < x), I₁.filter fun y => x < y] ++ tail) := by
    rw [stackOf_succ hleg, hst, step_active hx hgt hmem]
  exact ⟨by rw [Legal, h]; rfl, by rw [stack, h]; rfl⟩

/-- **Legal moves at a nonempty stack**: a base value, or a value of the active head. -/
theorem legal_succ_iff_cons (hleg : Legal n σ) {I₁ : Finset ℕ} {tail : List (Finset ℕ)}
    (hst : stack n σ = I₁ :: tail) :
    Legal n (σ ++ [x]) ↔ (x ∈ unread n σ ∧ (x < b2 n σ ∨ x ∈ I₁)) := by
  constructor
  · intro h
    have hx := h.mem_unread
    refine ⟨hx, ?_⟩
    by_contra hcon
    rw [not_or, Nat.not_lt] at hcon
    have hgt : b2 n σ < x := lt_of_le_of_ne hcon.1 (fun hc => b2_not_unread n σ (hc ▸ hx))
    rw [Legal, stackOf_succ hleg, hst, step_deferred hgt hcon.2] at h
    exact Bool.noConfusion h
  · rintro ⟨hx, hlt | hmem⟩
    · rcases mem_B0_or_B1_or_gt_b2 hx with h0 | h1 | hgt
      · exact ((legal_succ_of_band0 hleg h0).1)
      · exact ((legal_succ_of_band1_cons hleg hst h1).1)
      · omega
    · rcases mem_B0_or_B1_or_gt_b2 hx with h0 | h1 | hgt
      · exact ((legal_succ_of_band0 hleg h0).1)
      · exact ((legal_succ_of_band1_cons hleg hst h1).1)
      · exact ((legal_succ_of_active hleg hst hx hgt hmem).1)

/-- **Legal moves at an empty stack**: only a base value. -/
theorem legal_succ_iff_nil (hleg : Legal n σ) (hst : stack n σ = []) :
    Legal n (σ ++ [x]) ↔ (x ∈ unread n σ ∧ x < b2 n σ) := by
  constructor
  · intro h
    have hx := h.mem_unread
    refine ⟨hx, ?_⟩
    by_contra hcon
    rw [Nat.not_lt] at hcon
    have hgt : b2 n σ < x := lt_of_le_of_ne hcon (fun hc => b2_not_unread n σ (hc ▸ hx))
    rw [Legal, stackOf_succ hleg, hst, step_nil_above hgt] at h
    exact Bool.noConfusion h
  · rintro ⟨hx, hlt⟩
    rcases mem_B0_or_B1_or_gt_b2 hx with h0 | h1 | hgt
    · exact ((legal_succ_of_band0 hleg h0).1)
    · exact ((legal_succ_of_band1_nil hleg hst h1).1)
    · omega

/-! ### The ordered layout -/

/--
**The layout invariant** at `d = 2`, the paper's \eqref{eq:ordered-layout} together with the
run condition of \cref{sec:stack}: the intervals of the stack are nonempty, increasing,
their union is the set of unread values above the second threshold `b₂`, and each of them is
a run of the unread values.

The rest of \eqref{eq:ordered-layout}, `B₀ < b₁ < B₁ < b₂`, holds by the definitions of the
bands (`mem_B0`, `mem_B1`) together with `b1_lt_b2`; `union` is the assertion
`b₂ < I₁ < ⋯ < I_s` and that the `I_j` exhaust the unread values above `b₂`.
-/
structure Layout (n : ℕ) (σ : List ℕ) : Prop where
  /-- Every interval of the stack is nonempty. -/
  nonempty : ∀ I ∈ stack n σ, I.Nonempty
  /-- The intervals increase: `I₁ < I₂ < ⋯` elementwise. -/
  ordered : (stack n σ).Pairwise fun I J => ∀ a ∈ I, ∀ b ∈ J, a < b
  /-- The union of the intervals is the set of unread values above `b₂`. -/
  union : stackUnion (stack n σ) = (unread n σ).filter fun y => b2 n σ < y
  /-- Each interval is a run of the unread values. -/
  runs : ∀ I ∈ stack n σ, ∀ a ∈ I, ∀ b ∈ I, ∀ y ∈ unread n σ, a < y → y < b → y ∈ I

theorem Layout.mem_iff (h : Layout n σ) {y : ℕ} :
    (∃ I ∈ stack n σ, y ∈ I) ↔ (y ∈ unread n σ ∧ b2 n σ < y) := by
  rw [← mem_stackUnion, h.union, Finset.mem_filter]

theorem Layout.unread_of_mem (h : Layout n σ) {I : Finset ℕ} (hI : I ∈ stack n σ) {a : ℕ}
    (ha : a ∈ I) : a ∈ unread n σ := (h.mem_iff.mp ⟨I, hI, ha⟩).1

theorem Layout.lt_of_mem (h : Layout n σ) {I : Finset ℕ} (hI : I ∈ stack n σ) {a : ℕ}
    (ha : a ∈ I) : b2 n σ < a := (h.mem_iff.mp ⟨I, hI, ha⟩).2

theorem Layout.exists_mem (h : Layout n σ) {y : ℕ} (hy : y ∈ unread n σ) (hb : b2 n σ < y) :
    ∃ I ∈ stack n σ, y ∈ I := h.mem_iff.mpr ⟨hy, hb⟩

/-- **Distinct intervals of the stack are disjoint.** -/
theorem Layout.pairwiseDisjoint (h : Layout n σ) :
    (stack n σ).Pairwise fun I J => Disjoint I J := by
  refine h.ordered.imp ?_
  intro I J hIJ
  exact Finset.disjoint_left.mpr fun a ha hb => absurd (hIJ a ha a hb) (lt_irrefl a)

/-- The active head is an initial segment of the unread values above `b₂`. -/
theorem Layout.head_initial (h : Layout n σ) {I₁ : Finset ℕ} {tail : List (Finset ℕ)}
    (hst : stack n σ = I₁ :: tail) {y b : ℕ} (hy : y ∈ unread n σ) (hb2 : b2 n σ < y)
    (hb : b ∈ I₁) (hyb : y < b) : y ∈ I₁ := by
  obtain ⟨J, hJ, hyJ⟩ := h.exists_mem hy hb2
  rw [hst, List.mem_cons] at hJ
  rcases hJ with rfl | hJ
  · exact hyJ
  · have hpw := h.ordered
    rw [hst, List.pairwise_cons] at hpw
    exact absurd (hpw.1 J hJ b hb y hyJ) (by omega)

/-- **A nonempty stack forces `b₂` to be nonvirtual**: some unread value lies above it. -/
theorem Layout.b2_lt (h : Layout n σ) (hne : stack n σ ≠ []) : b2 n σ < n := by
  obtain ⟨I, tail, hst⟩ : ∃ I tail, stack n σ = I :: tail := by
    cases hs : stack n σ with
    | nil => exact absurd hs hne
    | cons I t => exact ⟨I, t, rfl⟩
  have hI : I ∈ stack n σ := by rw [hst]; exact List.mem_cons_self
  obtain ⟨a, ha⟩ := h.nonempty I hI
  have h1 := h.lt_of_mem hI ha
  have h2 := h.unread_of_mem hI ha
  rw [OneThreshold.mem_unread] at h2
  omega

/-- **\cref{lem:least-trigger-frontier} at a nonempty stack**: `b₂` is then a `2`-trigger of
the prefix, which is what the active-interval case of \cref{cor:separators} uses. -/
theorem Layout.isTrigger_b2 (h : Layout n σ) (hne : stack n σ ≠ []) :
    IsTrigger σ 2 (b2 n σ) :=
  _root_.Av12453.TwoThreshold.isTrigger_b2 (by have := h.b2_lt hne; omega)

/-- **The ordered layout is preserved by the scan.**  Every legal prefix satisfies
\eqref{eq:ordered-layout}. -/
theorem layout_of_legal (hleg : Legal n σ) : Layout n σ := by
  induction σ using List.reverseRecOn with
  | nil =>
    refine ⟨by simp, by simp, ?_, by simp⟩
    rw [stack_nil]
    change (∅ : Finset ℕ) = _
    symm
    rw [Finset.filter_eq_empty_iff]
    intro y hy
    rw [OneThreshold.mem_unread] at hy
    simp only [b2_nil]
    omega
  | append_singleton τ x ih =>
    have hτ : Legal n τ := hleg.of_append_singleton
    have hlay : Layout n τ := ih hτ
    have hw : IsWord n τ := hτ.isWord
    have hx : x ∈ unread n τ := hleg.mem_unread
    have hun : unread n (τ ++ [x]) = (unread n τ).erase x := unread_append_singleton
    have hb2not : b2 n τ ∉ unread n τ := b2_not_unread n τ
    rcases mem_B0_or_B1_or_gt_b2 hx with h0 | h1 | hgt
    · -- Early-band move: the stack does not change.
      obtain ⟨-, hstack⟩ := legal_succ_of_band0 hτ h0
      have hb2' : b2 n (τ ++ [x]) = b2 n τ := b2_succ_band0 (mem_B0.mp h0).2
      have hxb2 : x < b2 n τ := by
        have := (mem_B0.mp h0).2
        have := b1_lt_b2 n τ
        omega
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hstack]
      · exact hlay.nonempty
      · exact hlay.ordered
      · rw [hun, hb2', hlay.union]
        ext y
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hy, hb⟩; exact ⟨⟨by omega, hy⟩, hb⟩
        · rintro ⟨⟨-, hy⟩, hb⟩; exact ⟨hy, hb⟩
      · intro I hI a ha b hb y hy hay hyb
        rw [hun, Finset.mem_erase] at hy
        exact hlay.runs I hI a ha b hb y hy.2 hay hyb
    · -- Last-band move: `E = mergeSet` joins the head.
      have hx' := mem_B1.mp h1
      have hb2' : b2 n (τ ++ [x]) = x := b2_succ_band1 hx'.1 hx'.2.1 hx'.2.2
      cases hst : stack n τ with
      | cons I₁ tail =>
        have hI₁mem : I₁ ∈ stack n τ := by rw [hst]; exact List.mem_cons_self
        have htailmem : ∀ J ∈ tail, J ∈ stack n τ := by
          intro J hJ; rw [hst]; exact List.mem_cons_of_mem _ hJ
        obtain ⟨-, hstack⟩ := legal_succ_of_band1_cons hτ hst h1
        obtain ⟨hcross, hptail⟩ := List.pairwise_cons.mp (hst ▸ hlay.ordered)
        refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hstack]
        · intro I hI
          rcases List.mem_cons.mp hI with rfl | hI
          · obtain ⟨a, ha⟩ := hlay.nonempty I₁ hI₁mem
            exact ⟨a, Finset.mem_union_right _ ha⟩
          · exact hlay.nonempty I (htailmem I hI)
        · rw [List.pairwise_cons]
          refine ⟨?_, hptail⟩
          intro J hJ a ha b hb
          rcases Finset.mem_union.mp ha with haE | haI
          · have h1' : b2 n τ < b := hlay.lt_of_mem (htailmem J hJ) hb
            rw [mem_mergeSet] at haE
            omega
          · exact hcross J hJ a haI b hb
        · rw [hun, hb2']
          ext y
          constructor
          · intro hy
            rw [mem_stackUnion] at hy
            obtain ⟨I, hI, hyI⟩ := hy
            rcases List.mem_cons.mp hI with rfl | hI
            · rcases Finset.mem_union.mp hyI with h | h
              · rw [mem_mergeSet] at h
                exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨by omega, h.1⟩, h.2.1⟩
              · have hu := hlay.unread_of_mem hI₁mem h
                have hb := hlay.lt_of_mem hI₁mem h
                exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨by omega, hu⟩, by omega⟩
            · have hu := hlay.unread_of_mem (htailmem I hI) hyI
              have hb := hlay.lt_of_mem (htailmem I hI) hyI
              exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨by omega, hu⟩, by omega⟩
          · intro hy
            rw [Finset.mem_filter, Finset.mem_erase] at hy
            obtain ⟨⟨hyx, hyu⟩, hxy⟩ := hy
            rw [mem_stackUnion]
            rcases lt_trichotomy y (b2 n τ) with h | h | h
            · exact ⟨_, List.mem_cons_self,
                Finset.mem_union_left _ (mem_mergeSet.mpr ⟨hyu, hxy, h⟩)⟩
            · exact absurd (h ▸ hyu) hb2not
            · obtain ⟨I, hI, hyI⟩ := hlay.exists_mem hyu h
              rw [hst] at hI
              rcases List.mem_cons.mp hI with rfl | hI
              · exact ⟨_, List.mem_cons_self, Finset.mem_union_right _ hyI⟩
              · exact ⟨I, List.mem_cons_of_mem _ hI, hyI⟩
        · intro I hI a ha b hb y hy hay hyb
          rw [hun, Finset.mem_erase] at hy
          obtain ⟨hyx, hyu⟩ := hy
          rcases List.mem_cons.mp hI with rfl | hI
          · have hax : x < a := by
              rcases Finset.mem_union.mp ha with h | h
              · rw [mem_mergeSet] at h; omega
              · have := hlay.lt_of_mem hI₁mem h; omega
            rcases lt_trichotomy y (b2 n τ) with h | h | h
            · exact Finset.mem_union_left _ (mem_mergeSet.mpr ⟨hyu, by omega, h⟩)
            · exact absurd (h ▸ hyu) hb2not
            · have hbI₁ : b ∈ I₁ := by
                rcases Finset.mem_union.mp hb with hbE | hbI
                · rw [mem_mergeSet] at hbE; omega
                · exact hbI
              exact Finset.mem_union_right _ (hlay.head_initial hst hyu h hbI₁ hyb)
          · exact hlay.runs I (htailmem I hI) a ha b hb y hyu hay hyb
      | nil =>
        obtain ⟨-, hstack⟩ := legal_succ_of_band1_nil hτ hst h1
        have hempty : ∀ y, y ∈ unread n τ → ¬ (b2 n τ < y) := by
          intro y hy hb
          obtain ⟨I, hI, -⟩ := hlay.exists_mem hy hb
          rw [hst] at hI
          exact absurd hI (by simp)
        refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hstack]
        · intro I hI
          exact (mem_nzI.mp hI).2
        · exact List.Pairwise.sublist (nzI_sublist _) (by simp)
        · rw [hun, hb2', stackUnion_nzI, stackUnion_cons, stackUnion]
          simp only [List.foldr_nil, Finset.union_empty]
          ext y
          rw [mem_mergeSet, Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨hyu, hxy, hyb⟩
            exact ⟨⟨by omega, hyu⟩, hxy⟩
          · rintro ⟨⟨hyx, hyu⟩, hxy⟩
            refine ⟨hyu, hxy, ?_⟩
            rcases lt_trichotomy y (b2 n τ) with h | h | h
            · exact h
            · exact absurd (h ▸ hyu) hb2not
            · exact absurd h (hempty y hyu)
        · intro I hI a ha b hb y hy hay hyb
          rw [mem_nzI] at hI
          rw [List.mem_singleton] at hI
          rw [hI.1] at ha hb ⊢
          rw [mem_mergeSet] at ha hb ⊢
          rw [hun, Finset.mem_erase] at hy
          exact ⟨hy.2, by omega, by omega⟩
    · -- Active-interval move: the head splits.
      have hb2' : b2 n (τ ++ [x]) = b2 n τ := b2_succ_above hx hgt
      cases hst : stack n τ with
      | nil =>
        have := ((legal_succ_iff_nil hτ hst).mp hleg).2
        omega
      | cons I₁ tail =>
        have hI₁mem : I₁ ∈ stack n τ := by rw [hst]; exact List.mem_cons_self
        have htailmem : ∀ J ∈ tail, J ∈ stack n τ := by
          intro J hJ; rw [hst]; exact List.mem_cons_of_mem _ hJ
        have hmem : x ∈ I₁ :=
          ((legal_succ_iff_cons hτ hst).mp hleg).2.resolve_left (by omega)
        obtain ⟨-, hstack⟩ := legal_succ_of_active hτ hst hx hgt hmem
        obtain ⟨hcross, hptail⟩ := List.pairwise_cons.mp (hst ▸ hlay.ordered)
        have hsub : ∀ I ∈ nzI [I₁.filter (· < x), I₁.filter fun y => x < y], I ⊆ I₁ := by
          intro I hI
          rw [mem_nzI] at hI
          rcases List.mem_cons.mp hI.1 with rfl | hI'
          · exact Finset.filter_subset _ _
          · rw [List.mem_singleton.mp hI']
            exact Finset.filter_subset _ _
        refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hstack]
        · intro I hI
          rcases List.mem_append.mp hI with hI | hI
          · exact (mem_nzI.mp hI).2
          · exact hlay.nonempty I (htailmem I hI)
        · rw [List.pairwise_append]
          refine ⟨List.Pairwise.sublist (nzI_sublist _) ?_, hptail, ?_⟩
          · rw [List.pairwise_cons]
            refine ⟨?_, by simp⟩
            intro J hJ a ha b hb
            rw [List.mem_singleton.mp hJ] at hb
            simp only [Finset.mem_filter] at ha hb
            omega
          · intro C hC J hJ a ha b hb
            exact hcross J hJ a (hsub C hC ha) b hb
        · rw [hun, hb2', stackUnion_append, stackUnion_nzI]
          have hu := hlay.union
          rw [hst, stackUnion_cons] at hu
          have hxtail : x ∉ stackUnion tail := by
            rw [mem_stackUnion]
            rintro ⟨J, hJ, hxJ⟩
            exact absurd (hcross J hJ x hmem x hxJ) (by omega)
          have hAB : I₁.filter (· < x) ∪ I₁.filter (fun y => x < y) = I₁.erase x := by
            ext y
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
            constructor
            · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;> exact ⟨by omega, ha⟩
            · rintro ⟨ha, hb⟩
              rcases lt_trichotomy y x with h | h | h
              · exact Or.inl ⟨hb, h⟩
              · exact absurd h ha
              · exact Or.inr ⟨hb, h⟩
          have hSU : stackUnion [I₁.filter (· < x), I₁.filter fun y => x < y]
              = I₁.filter (· < x) ∪ I₁.filter (fun y => x < y) := by
            simp [stackUnion]
          rw [hSU, hAB, Finset.filter_erase, ← hu, Finset.erase_union_distrib,
            Finset.erase_eq_of_notMem hxtail]
        · intro I hI a ha b hb y hy hay hyb
          rw [hun, Finset.mem_erase] at hy
          obtain ⟨hyx, hyu⟩ := hy
          rcases List.mem_append.mp hI with hI | hI
          · have hIsub := hsub I hI
            have hyI₁ : y ∈ I₁ := hlay.runs I₁ hI₁mem a (hIsub ha) b (hIsub hb) y hyu hay hyb
            rw [mem_nzI] at hI
            rcases List.mem_cons.mp hI.1 with rfl | hI'
            · simp only [Finset.mem_filter] at ha hb ⊢
              exact ⟨hyI₁, by omega⟩
            · rw [List.mem_singleton.mp hI'] at ha hb ⊢
              simp only [Finset.mem_filter] at ha hb ⊢
              exact ⟨hyI₁, by omega⟩
          · exact hlay.runs I (htailmem I hI) a ha b hb y hyu hay hyb

/-- Every interval size is positive, so `H` is always evaluated at a genuine composition. -/
theorem L_pos (hleg : Legal n σ) : ∀ a ∈ L n σ, 0 < a := by
  intro a ha
  rw [L, List.mem_map] at ha
  obtain ⟨I, hI, rfl⟩ := ha
  exact Finset.card_pos.mpr ((layout_of_legal hleg).nonempty I hI)

theorem nz_L (hleg : Legal n σ) : nz (L n σ) = L n σ :=
  nz_eq_self fun a ha => by have := L_pos hleg a ha; omega

/-! ### The measure `ρ = ‖𝐩‖₁ + |L|`

The paper's \eqref{eq:rho} at `d = 2`: the control mass `p₀ + p₁` plus the total interval
size is the number of unread values, and it drops by one at every move.  This is the measure
on which the induction proving `A_eq_H` runs, and the one that makes the fuel-driven
definition of `H` below terminate. -/

/-- Every move drops the number of unread values by one. -/
theorem card_unread_succ (hleg : Legal n (σ ++ [x])) :
    (unread n (σ ++ [x])).card + 1 = (unread n σ).card := by
  rw [unread_append_singleton, Finset.card_erase_of_mem hleg.mem_unread]
  have := Finset.card_pos.mpr ⟨x, hleg.mem_unread⟩
  omega

/-- **The measure** \eqref{eq:rho} at `d = 2`: `ρ(𝐩, L) = p₀ + p₁ + |L|` is the number of
unread values. -/
theorem rho_eq (hleg : Legal n σ) :
    (p n σ).1 + (p n σ).2 + (L n σ).sum = (unread n σ).card := by
  have hlay := layout_of_legal hleg
  rw [L, ← card_stackUnion _ hlay.ordered, hlay.union, controlMass_eq]
  have hsplit : unread n σ =
      (unread n σ).filter (fun y => y < b2 n σ) ∪ (unread n σ).filter fun y => b2 n σ < y := by
    ext y
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hy
      rcases lt_trichotomy y (b2 n σ) with h | h | h
      · exact Or.inl ⟨hy, h⟩
      · exact absurd (h ▸ hy) (b2_not_unread n σ)
      · exact Or.inr ⟨hy, h⟩
    · rintro (⟨hy, -⟩ | ⟨hy, -⟩) <;> exact hy
  conv_rhs => rw [hsplit]
  rw [Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_filter] at ha hb
  omega

/-! ### The transition of `(𝐩, L)`

The four groups of \eqref{eq:H}: an early-band move (\eqref{eq:T} at `i = 0`), a last-band
move (\eqref{eq:U}, with the merger of \cref{lem:merger}), and the two shapes of an
active-interval move (\cref{lem:first-letter}), which for the sizes are the endpoint and
interior terms. -/

/-- The paper's `δ_h`: `x ∈ B₁` splits the last band into the `h = below1` values below it
and the `δ_h = p₁ - 1 - h` values of `E = mergeSet n σ x` above it. -/
theorem card_mergeSet (hx : x ∈ B1 n σ) :
    below1 n σ x + 1 + (mergeSet n σ x).card = (p n σ).2 := by
  rw [mergeSet_eq_band1_gt hx]
  exact card_filter_lt_add_card_filter_gt hx

theorem card_mergeSet_eq (hx : x ∈ B1 n σ) :
    (mergeSet n σ x).card = (p n σ).2 - 1 - below1 n σ x := by
  have := card_mergeSet hx
  omega

/-- **The early-band transition**, \eqref{eq:T} at `i = 0`: the control becomes
`(h, p₁ + p₀ - 1 - h)` with `h` the number of band-`0` values below `x`, and the stack -- so
also `L` -- does not change. -/
theorem pL_succ_band0 (hleg : Legal n σ) (hx : x ∈ B0 n σ) :
    Legal n (σ ++ [x]) ∧
      p n (σ ++ [x]) = (below0 n σ x, (p n σ).2 + (p n σ).1 - 1 - below0 n σ x) ∧
      L n (σ ++ [x]) = L n σ :=
  ⟨(legal_succ_of_band0 hleg hx).1, p_succ_band0 hx, by
    rw [L, L, (legal_succ_of_band0 hleg hx).2]⟩

/-- **The last-band transition** at a nonempty stack, \eqref{eq:U} with the merger: the
control becomes `(p₀, h)` and the active head grows from `ℓ₁` to `ℓ₁ + δ_h`. -/
theorem pL_succ_band1_cons (hleg : Legal n σ) {I₁ : Finset ℕ} {tail : List (Finset ℕ)}
    (hst : stack n σ = I₁ :: tail) (hx : x ∈ B1 n σ) :
    Legal n (σ ++ [x]) ∧
      p n (σ ++ [x]) = ((p n σ).1, below1 n σ x) ∧
      L n (σ ++ [x]) =
        (I₁.card + ((p n σ).2 - 1 - below1 n σ x)) :: tail.map Finset.card := by
  refine ⟨(legal_succ_of_band1_cons hleg hst hx).1, p_succ_band1 hx, ?_⟩
  rw [L, (legal_succ_of_band1_cons hleg hst hx).2, List.map_cons]
  have hlay := layout_of_legal hleg
  have hI₁ : I₁ ∈ stack n σ := by rw [hst]; exact List.mem_cons_self
  have hdisj : Disjoint (mergeSet n σ x) I₁ := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [mem_mergeSet] at ha
    exact absurd (hlay.lt_of_mem hI₁ hb) (by omega)
  rw [Finset.card_union_of_disjoint hdisj, card_mergeSet_eq hx]
  congr 1
  omega

/-- **The last-band transition** at an empty stack: the merger set becomes the whole stack,
and is dropped when it is empty. -/
theorem pL_succ_band1_nil (hleg : Legal n σ) (hst : stack n σ = []) (hx : x ∈ B1 n σ) :
    Legal n (σ ++ [x]) ∧
      p n (σ ++ [x]) = ((p n σ).1, below1 n σ x) ∧
      L n (σ ++ [x]) = nz [(p n σ).2 - 1 - below1 n σ x] := by
  refine ⟨(legal_succ_of_band1_nil hleg hst hx).1, p_succ_band1 hx, ?_⟩
  rw [L, (legal_succ_of_band1_nil hleg hst hx).2, map_card_nzI]
  simp only [List.map_cons, List.map_nil, card_mergeSet_eq hx]

/-- **The active-interval transition**: reading the value of local rank `r + 1` of the head
replaces the head by the two parts of sizes `r` and `ℓ₁ - 1 - r`, with empty parts deleted;
the control does not change.  The two endpoints (`r = 0` and `r = ℓ₁ - 1`) give the endpoint
term of \eqref{eq:H} and an interior value of local rank `j = r + 1` gives the interior
term. -/
theorem pL_succ_active (hleg : Legal n σ) {I₁ : Finset ℕ} {tail : List (Finset ℕ)}
    (hst : stack n σ = I₁ :: tail) (hx : x ∈ unread n σ) (hgt : b2 n σ < x) (hmem : x ∈ I₁) :
    Legal n (σ ++ [x]) ∧ p n (σ ++ [x]) = p n σ ∧
      L n (σ ++ [x]) =
        nz [(I₁.filter (· < x)).card, I₁.card - 1 - (I₁.filter (· < x)).card]
          ++ tail.map Finset.card := by
  refine ⟨(legal_succ_of_active hleg hst hx hgt hmem).1, p_succ_above hx hgt, ?_⟩
  rw [L, (legal_succ_of_active hleg hst hx hgt hmem).2, List.map_append, map_card_nzI]
  have hsplit := card_filter_lt_add_card_filter_gt hmem
  have hB : (I₁.filter fun y => x < y).card = I₁.card - 1 - (I₁.filter (· < x)).card := by omega
  simp only [List.map_cons, List.map_nil, hB]

/-- The in-band rank of a band-`0` value is below `p₀`. -/
theorem below0_lt (hx : x ∈ B0 n σ) : below0 n σ x < (p n σ).1 :=
  rank_lt_card hx

/-- The in-band rank of a band-`1` value is below `p₁`. -/
theorem below1_lt (hx : x ∈ B1 n σ) : below1 n σ x < (p n σ).2 :=
  rank_lt_card hx

/-- **The three groups of next letters.**  The unread values split into the two bands and
the values above `b₂`; this is how `A_succ`'s sum over letters is regrouped into
\eqref{eq:H}. -/
theorem sum_unread_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ x ∈ unread n σ, f x
      = (∑ x ∈ B0 n σ, f x) + (∑ x ∈ B1 n σ, f x)
        + ∑ x ∈ (unread n σ).filter (fun y => b2 n σ < y), f x := by
  have hb := b1_lt_b2 n σ
  have h01 : Disjoint (B0 n σ) (B1 n σ) := by
    rw [Finset.disjoint_left]
    intro a ha hb'
    rw [mem_B0] at ha
    rw [mem_B1] at hb'
    omega
  have hu : (B0 n σ ∪ B1 n σ) ∪ (unread n σ).filter (fun y => b2 n σ < y) = unread n σ := by
    ext y
    simp only [Finset.mem_union, Finset.mem_filter, mem_B0, mem_B1]
    constructor
    · rintro ((⟨hy, -⟩ | ⟨hy, -, -⟩) | ⟨hy, -⟩) <;> exact hy
    · intro hy
      rcases mem_B0_or_B1_or_gt_b2 hy with h | h | h
      · exact Or.inl (Or.inl (mem_B0.mp h))
      · exact Or.inl (Or.inr (mem_B1.mp h))
      · exact Or.inr ⟨hy, h⟩
  have h2 : Disjoint (B0 n σ ∪ B1 n σ) ((unread n σ).filter fun y => b2 n σ < y) := by
    rw [Finset.disjoint_left]
    intro a ha hb'
    rw [Finset.mem_filter] at hb'
    rcases Finset.mem_union.mp ha with h | h
    · rw [mem_B0] at h; omega
    · rw [mem_B1] at h; omega
  conv_lhs => rw [← hu]
  rw [Finset.sum_union h2, Finset.sum_union h01]

/-! ### Adjacency and separations

`Adjacent` is reused verbatim from the one-threshold development; `Sep` is
\cref{cor:separators}(ii) at `d = 2` and `DiffIntervals` is \cref{cor:separators}(i).  The
only difference from `d = 1` is that `c` must be a `2`-trigger, not merely a read letter. -/

set_option linter.unusedVariables false in
/--
The separation predicate of \cref{cor:separators}(ii) at `d = 2`: some letter `z` with
`u < z < v` was read after a `2`-trigger `c < u`.  (For `d = 1` every read letter is a
trigger, which is why `Av12453.OneThreshold.Sep` lets `c` range over all read letters.)
-/
def Sep (n : ℕ) (σ : List ℕ) (u v : ℕ) : Prop :=
  ∃ c z, IsTrigger σ 2 c ∧ z ∈ σ ∧ σ.idxOf c < σ.idxOf z ∧ c < u ∧ u < z ∧ z < v

/-- `u` and `v` lie in different intervals of the stack: \cref{cor:separators}(i). -/
def DiffIntervals (n : ℕ) (σ : List ℕ) (u v : ℕ) : Prop :=
  ¬ ∃ I ∈ stack n σ, u ∈ I ∧ v ∈ I

/-- A `2`-trigger value is a letter of the prefix. -/
theorem mem_of_isTrigger_two {c : ℕ} (h : IsTrigger σ 2 c) : c ∈ σ :=
  mem_of_mem_trigVals (mem_trigVals_iff.mpr h)

theorem Sep.mem {u v : ℕ} (h : Sep n σ u v) : ∃ c ∈ σ, IsTrigger σ 2 c ∧ c < u := by
  obtain ⟨c, z, htc, -, -, hcu, -, -⟩ := h
  exact ⟨c, mem_of_isTrigger_two htc, htc, hcu⟩

/-- **The explicit form of `Sep`**: unfolding "`c` is a `2`-trigger" to its witness `a`.
This is the shape used to build a `12453`-occurrence `a, c, z, x, y`. -/
theorem sep_iff_explicit (hnd : σ.Nodup) {u v : ℕ} :
    Sep n σ u v ↔
      ∃ a c z, a ∈ σ ∧ c ∈ σ ∧ z ∈ σ ∧ σ.idxOf a < σ.idxOf c ∧ σ.idxOf c < σ.idxOf z ∧
        a < c ∧ c < u ∧ u < z ∧ z < v := by
  constructor
  · rintro ⟨c, z, htc, hz, hcz, hcu, huz, hzv⟩
    obtain ⟨hc, a, ha, hac, hlt⟩ := (isTrigger_two_iff hnd).mp htc
    exact ⟨a, c, z, ha, hc, hz, hac, hcz, hlt, hcu, huz, hzv⟩
  · rintro ⟨a, c, z, ha, hc, hz, hac, hcz, hlt, hcu, huz, hzv⟩
    exact ⟨c, z, (isTrigger_two_iff hnd).mpr ⟨hc, a, ha, hac, hlt⟩, hz, hcz, hcu, huz, hzv⟩

/-! ### The two-threshold recurrence `H`

The recurrence is the paper's \eqref{eq:H} at `d = 2` together with
\eqref{eq:initial-terminal}.  It is defined by recursion on the fuel `k`, with `H 𝐩 L`
evaluating the body with `k = p₀ + p₁ + |L| + 1`; `Haux_congr` shows that any sufficient
amount of fuel gives the same value, and `H_eq_nil`, `H_eq_cons` and `H_endpoint` are the
defining equations.  On a list with a zero entry -- a state that never occurs along the
scan, since the intervals of the stack are nonempty (`L_pos`) -- `H` is `0`.

The dictionary with \eqref{eq:H}, writing `𝐩 = (p₀, p₁)` and `L = ℓ₁ :: L'`:

* line 1, the early-band sum `∑_{h<p₀} H_{T_{0,h}(𝐩)}(L)`, is
  `∑ h ∈ range q.1, H (h, q.2 + q.1 - 1 - h) L`, since
  `T_{0,h}(p₀,p₁) = (h, p₁ + p₀ - 1 - h)` by \eqref{eq:T};
* line 2, the last-band sum `∑_{h<p₁} H_{U_h(𝐩)}(\nz(ℓ₁+δ_h, ℓ₂, …))`, is
  `∑ h ∈ range q.2, H (q.1, h) ((ℓ₁ + (q.2 - 1 - h)) :: L')` at a nonempty stack -- where
  `U_h(𝐩) = (p₀, h)` and `δ_h = p₁ - 1 - h` by \eqref{eq:U}, and `\nz` is not needed
  because `ℓ₁ ≥ 1` -- and `∑ h ∈ range q.2, H (q.1, h) (nz [q.2 - 1 - h])` at an empty
  stack, where `ℓ₁ = 0` and `\nz` does delete an empty merger set;
* line 3, the endpoint term `1_{ℓ₁>0} min(2,ℓ₁) H_𝐩(\nz(ℓ₁-1, ℓ₂, …))`, is `Eend ℓ₁ 𝐩 L'`;
  it is absent at an empty stack;
* line 4, the interior sum `∑_{j=2}^{ℓ₁-1} H_𝐩((j-1, ℓ₁-j, ℓ₂, …))`, is
  `∑ a ∈ Finset.Ico 1 (ℓ₁ - 1), H 𝐩 (a :: (ℓ₁ - 1 - a) :: L')` under `a = j - 1`; it is
  absent at an empty stack.

`H_zero` is the terminal condition `H_𝟎(∅) = 1` of \eqref{eq:initial-terminal}, and
`av12453_count` (component 3b's goal, proved in `Av12453.TwoThreshold.Counting`) is its
initial condition `a_n^{(2)} = H_{(n,0)}(∅)`. -/

/-- Fuel-driven evaluation of the two-threshold recurrence. -/
private def Haux : ℕ → ℕ × ℕ → List ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, q, [] =>
      (if q = (0, 0) then 1 else 0)
        + (∑ h ∈ Finset.range q.1, Haux k (h, q.2 + q.1 - 1 - h) [])
        + ∑ h ∈ Finset.range q.2, Haux k (q.1, h) (nz [q.2 - 1 - h])
  | _ + 1, _, 0 :: _ => 0
  | k + 1, q, (ℓ + 1) :: L' =>
      (∑ h ∈ Finset.range q.1, Haux k (h, q.2 + q.1 - 1 - h) ((ℓ + 1) :: L'))
        + (∑ h ∈ Finset.range q.2, Haux k (q.1, h) ((ℓ + 1 + (q.2 - 1 - h)) :: L'))
        + (if ℓ = 0 then Haux k q L' else 2 * Haux k q (ℓ :: L'))
        + ∑ a ∈ Finset.Ico 1 ℓ, Haux k q (a :: (ℓ - a) :: L')

private theorem Haux_nil (k : ℕ) (q : ℕ × ℕ) :
    Haux (k + 1) q [] =
      (if q = (0, 0) then 1 else 0)
        + (∑ h ∈ Finset.range q.1, Haux k (h, q.2 + q.1 - 1 - h) [])
        + ∑ h ∈ Finset.range q.2, Haux k (q.1, h) (nz [q.2 - 1 - h]) := rfl

private theorem Haux_zero (k : ℕ) (q : ℕ × ℕ) (L' : List ℕ) : Haux (k + 1) q (0 :: L') = 0 :=
  rfl

private theorem Haux_cons (k : ℕ) (q : ℕ × ℕ) (ℓ : ℕ) (L' : List ℕ) :
    Haux (k + 1) q ((ℓ + 1) :: L') =
      (∑ h ∈ Finset.range q.1, Haux k (h, q.2 + q.1 - 1 - h) ((ℓ + 1) :: L'))
        + (∑ h ∈ Finset.range q.2, Haux k (q.1, h) ((ℓ + 1 + (q.2 - 1 - h)) :: L'))
        + (if ℓ = 0 then Haux k q L' else 2 * Haux k q (ℓ :: L'))
        + ∑ a ∈ Finset.Ico 1 ℓ, Haux k q (a :: (ℓ - a) :: L') := rfl

/-- Any two amounts of fuel exceeding the measure `ρ(𝐩, L) = p₀ + p₁ + |L|` give the same
value. -/
private theorem Haux_congr : ∀ k k' (q : ℕ × ℕ) (l : List ℕ),
    q.1 + q.2 + l.sum < k → q.1 + q.2 + l.sum < k' → Haux k q l = Haux k' q l := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro k' q l h1 h2
    obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
    obtain ⟨k1, rfl⟩ : ∃ k1, k' = k1 + 1 := ⟨k' - 1, by omega⟩
    match l with
    | [] =>
      simp only [List.sum_nil, Nat.add_zero] at h1 h2
      rw [Haux_nil, Haux_nil]
      have e1 : ∀ h ∈ Finset.range q.1,
          Haux k0 (h, q.2 + q.1 - 1 - h) [] = Haux k1 (h, q.2 + q.1 - 1 - h) [] := by
        intro h hh
        rw [Finset.mem_range] at hh
        exact ih k0 (by omega) k1 _ [] (by simp; omega) (by simp; omega)
      have e2 : ∀ h ∈ Finset.range q.2,
          Haux k0 (q.1, h) (nz [q.2 - 1 - h]) = Haux k1 (q.1, h) (nz [q.2 - 1 - h]) := by
        intro h hh
        rw [Finset.mem_range] at hh
        exact ih k0 (by omega) k1 _ _ (by simp; omega) (by simp; omega)
      rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
    | 0 :: L' => rw [Haux_zero, Haux_zero]
    | (ℓ + 1) :: L' =>
      simp only [List.sum_cons] at h1 h2
      rw [Haux_cons, Haux_cons]
      have e1 : ∀ h ∈ Finset.range q.1,
          Haux k0 (h, q.2 + q.1 - 1 - h) ((ℓ + 1) :: L')
            = Haux k1 (h, q.2 + q.1 - 1 - h) ((ℓ + 1) :: L') := by
        intro h hh
        rw [Finset.mem_range] at hh
        exact ih k0 (by omega) k1 _ _ (by simp; omega) (by simp; omega)
      have e2 : ∀ h ∈ Finset.range q.2,
          Haux k0 (q.1, h) ((ℓ + 1 + (q.2 - 1 - h)) :: L')
            = Haux k1 (q.1, h) ((ℓ + 1 + (q.2 - 1 - h)) :: L') := by
        intro h hh
        rw [Finset.mem_range] at hh
        exact ih k0 (by omega) k1 _ _ (by simp; omega) (by simp; omega)
      have e3 : ∀ a ∈ Finset.Ico 1 ℓ,
          Haux k0 q (a :: (ℓ - a) :: L') = Haux k1 q (a :: (ℓ - a) :: L') := by
        intro a ha
        rw [Finset.mem_Ico] at ha
        exact ih k0 (by omega) k1 _ _ (by simp; omega) (by simp; omega)
      have e4 : Haux k0 q L' = Haux k1 q L' := ih k0 (by omega) k1 q L' (by omega) (by omega)
      have e5 : Haux k0 q (ℓ :: L') = Haux k1 q (ℓ :: L') :=
        ih k0 (by omega) k1 q _ (by simp; omega) (by simp; omega)
      rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3, e4, e5]

/--
`H 𝐩 L` is the paper's `H_{\mathbf p}(L)` at `d = 2`: the number of `12453`-avoiding
completions of a scanned prefix whose control is `𝐩 = (p₀, p₁)` and whose interval sizes
are `L`.
-/
def H (q : ℕ × ℕ) (l : List ℕ) : ℕ := Haux (q.1 + q.2 + l.sum + 1) q l

private theorem H_eq_Haux {q : ℕ × ℕ} {l : List ℕ} {k : ℕ} (hk : q.1 + q.2 + l.sum < k) :
    H q l = Haux k q l :=
  Haux_congr _ _ _ _ (by omega) hk

/-- The endpoint term of \eqref{eq:H}: `1_{ℓ₁>0} min(2, ℓ₁) H_𝐩(\nz(ℓ₁ - 1, ℓ₂, …))`. -/
def Eend (ℓ : ℕ) (q : ℕ × ℕ) (L' : List ℕ) : ℕ :=
  if ℓ = 1 then H q L' else 2 * H q ((ℓ - 1) :: L')

/-- **The endpoint term**, line 3 of \eqref{eq:H}. -/
theorem H_endpoint (ℓ : ℕ) (q : ℕ × ℕ) (L' : List ℕ) :
    Eend ℓ q L' = if ℓ = 1 then H q L' else 2 * H q ((ℓ - 1) :: L') := rfl

theorem H_endpoint_one (q : ℕ × ℕ) (L' : List ℕ) : Eend 1 q L' = H q L' := by
  simp [Eend]

theorem H_endpoint_two_le {ℓ : ℕ} (h : 2 ≤ ℓ) (q : ℕ × ℕ) (L' : List ℕ) :
    Eend ℓ q L' = 2 * H q ((ℓ - 1) :: L') := by
  rw [Eend, if_neg (by omega)]

/-- **\eqref{eq:H} at an empty stack**, together with the terminal condition
`H_𝟎(∅) = 1` of \eqref{eq:initial-terminal}: only the two base-value sums survive. -/
theorem H_eq_nil (q : ℕ × ℕ) :
    H q [] = (if q = (0, 0) then 1 else 0)
      + (∑ h ∈ Finset.range q.1, H (h, q.2 + q.1 - 1 - h) [])
      + ∑ h ∈ Finset.range q.2, H (q.1, h) (nz [q.2 - 1 - h]) := by
  rw [show H q [] = Haux (q.1 + q.2 + 1) q [] from H_eq_Haux (by simp), Haux_nil]
  have e1 : ∀ h ∈ Finset.range q.1,
      Haux (q.1 + q.2) (h, q.2 + q.1 - 1 - h) [] = H (h, q.2 + q.1 - 1 - h) [] := by
    intro h hh
    rw [Finset.mem_range] at hh
    exact (H_eq_Haux (by simp; omega)).symm
  have e2 : ∀ h ∈ Finset.range q.2,
      Haux (q.1 + q.2) (q.1, h) (nz [q.2 - 1 - h]) = H (q.1, h) (nz [q.2 - 1 - h]) := by
    intro h hh
    rw [Finset.mem_range] at hh
    exact (H_eq_Haux (by simp; omega)).symm
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]

/-- **\eqref{eq:H} at a nonempty stack** with active head of size `ℓ ≥ 1`: the four groups
are, in order, the early-band sum, the last-band sum, the endpoint term and the interior
sum. -/
theorem H_eq_cons {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (q : ℕ × ℕ) (L' : List ℕ) :
    H q (ℓ :: L') =
      (∑ h ∈ Finset.range q.1, H (h, q.2 + q.1 - 1 - h) (ℓ :: L'))
        + (∑ h ∈ Finset.range q.2, H (q.1, h) ((ℓ + (q.2 - 1 - h)) :: L'))
        + Eend ℓ q L'
        + ∑ a ∈ Finset.Ico 1 (ℓ - 1), H q (a :: (ℓ - 1 - a) :: L') := by
  obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
  rw [H, List.sum_cons,
    show q.1 + q.2 + (j + 1 + L'.sum) + 1 = (q.1 + q.2 + j + L'.sum + 1) + 1 by omega,
    Haux_cons]
  have e1 : ∀ h ∈ Finset.range q.1,
      Haux (q.1 + q.2 + j + L'.sum + 1) (h, q.2 + q.1 - 1 - h) ((j + 1) :: L')
        = H (h, q.2 + q.1 - 1 - h) ((j + 1) :: L') := by
    intro h hh
    rw [Finset.mem_range] at hh
    exact (H_eq_Haux (by simp; omega)).symm
  have e2 : ∀ h ∈ Finset.range q.2,
      Haux (q.1 + q.2 + j + L'.sum + 1) (q.1, h) ((j + 1 + (q.2 - 1 - h)) :: L')
        = H (q.1, h) ((j + 1 + (q.2 - 1 - h)) :: L') := by
    intro h hh
    rw [Finset.mem_range] at hh
    exact (H_eq_Haux (by simp; omega)).symm
  have e3 : ∀ a ∈ Finset.Ico 1 j,
      Haux (q.1 + q.2 + j + L'.sum + 1) q (a :: (j - a) :: L') = H q (a :: (j - a) :: L') := by
    intro a ha
    rw [Finset.mem_Ico] at ha
    exact (H_eq_Haux (by simp; omega)).symm
  have hE : (if j = 0 then Haux (q.1 + q.2 + j + L'.sum + 1) q L'
        else 2 * Haux (q.1 + q.2 + j + L'.sum + 1) q (j :: L')) = Eend (j + 1) q L' := by
    rw [Eend]
    by_cases hj : j = 0
    · subst hj
      rw [if_pos rfl, if_pos rfl]
      exact (H_eq_Haux (by omega)).symm
    · rw [if_neg hj, if_neg (show ¬ (j + 1 = 1) by omega), Nat.add_sub_cancel]
      exact congrArg _ (H_eq_Haux (by simp; omega)).symm
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3, hE,
    Nat.add_sub_cancel]

/-- A state with an empty interval is unreachable, and gets the value `0`. -/
theorem H_zero_head (q : ℕ × ℕ) (L' : List ℕ) : H q (0 :: L') = 0 := by
  rw [H, List.sum_cons, Nat.zero_add]
  cases h : q.1 + q.2 + L'.sum with
  | zero => rw [Haux_zero]
  | succ k => rw [Haux_zero]

/-- **The terminal condition** of \eqref{eq:initial-terminal}: `H_𝟎(∅) = 1`. -/
@[simp] theorem H_zero : H (0, 0) [] = 1 := by
  rw [H_eq_nil]
  simp

/-! ### Counting avoiders with a given prefix

`perms`, `avoiders` and the two prefix lemmas are pattern-generic and reused from the
one-threshold development; only `A` itself is specialized to `β₂ = 12453`. -/

/-- `A n σ` is the number of `12453`-avoiding permutations of `{0, …, n-1}` that begin with
the prefix `σ`. -/
def A (n : ℕ) (σ : List ℕ) : ℕ :=
  ((perms n).filter fun w => σ <+: w ∧ Avoids w (beta 2)).card

theorem A_nil (n : ℕ) : A n [] = (avoiders n (beta 2)).card := by
  rw [A, avoiders]
  exact congrArg _ (Finset.filter_congr fun w _ => by simp)

/-- **The prefix partition.**  With at least one letter left to read, the avoiders with
prefix `σ` are partitioned by their next letter, which ranges over the unread values. -/
theorem A_succ (n : ℕ) (σ : List ℕ) (hlen : σ.length < n) :
    A n σ = ∑ x ∈ unread n σ, A n (σ ++ [x]) := by
  have hmaps : ∀ w ∈ (perms n).filter fun w => σ <+: w ∧ Avoids w (beta 2),
      w.getD σ.length 0 ∈ unread n σ := by
    intro w hw
    rw [Finset.mem_filter, mem_perms] at hw
    exact getD_mem_unread hw.1 hw.2.1 hlen
  rw [A, Finset.card_eq_sum_card_fiberwise (fun w hw => hmaps w (Finset.mem_coe.mp hw))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [A, Finset.filter_filter]
  refine congrArg _ (Finset.filter_congr fun w hw => ?_)
  rw [mem_perms] at hw
  rw [prefix_append_singleton_iff (by rw [hw.length]; exact hlen)]
  tauto

/-- **The complete prefix.**  A prefix of full length is the permutation itself. -/
theorem A_complete (n : ℕ) (σ : List ℕ) (hw : IsWord n σ) (hlen : σ.length = n) :
    A n σ = if Avoids σ (beta 2) then 1 else 0 := by
  have hperm : IsPermOf n σ := isPermOf_of_isWord hw hlen
  have hset : ((perms n).filter fun w => σ <+: w ∧ Avoids w (beta 2))
      = if Avoids σ (beta 2) then {σ} else ∅ := by
    ext w
    rw [Finset.mem_filter, mem_perms]
    by_cases hav : Avoids σ (beta 2)
    · rw [if_pos hav, Finset.mem_singleton]
      constructor
      · rintro ⟨hw, hp, -⟩
        exact (hp.eq_of_length (by rw [hw.length, hlen])).symm
      · rintro rfl
        exact ⟨hperm, List.prefix_rfl, hav⟩
    · rw [if_neg hav]
      constructor
      · rintro ⟨hw, hp, hav'⟩
        exact absurd ((hp.eq_of_length (by rw [hw.length, hlen])) ▸ hav') hav
      · intro hmem
        exact absurd hmem (by simp)
  rw [A, hset]
  by_cases hav : Avoids σ (beta 2) <;> simp [hav]

/-! ### The four main theorems as hypotheses

The four theorems (A)--(D) of component 3b are proved in the sibling modules
`Av12453.TwoThreshold.{Invariant, Semantics, Counting}`.  Following the recommendation of
the component-3a report (development notes, in git history) §11, the statements of (A), (B) and
(C) are recorded here as
`Prop`-valued definitions, so that the modules proving (B), (C) and (D) can be stated
*relative* to them (`_of` variants) and compiled in parallel with, and independently of, the
proof of (A). -/

/-- **Statement (A)**, the separation criterion \cref{cor:separators} (i) ⟺ (ii) at
`d = 2`: for a legal prefix and an adjacent unread pair above `b₂`, lying in different
intervals of the stack is the same as being separated by a letter read after a smaller
`2`-trigger. -/
def SepInvariant (n : ℕ) : Prop :=
  ∀ {σ : List ℕ} {u v : ℕ}, Legal n σ → Adjacent n σ u v → b2 n σ < u →
    (DiffIntervals n σ u v ↔ Sep n σ u v)

/-- **Statement (B)**: a letter of a deferred interval has no `12453`-avoiding completion. -/
def DeferredHyp : Prop :=
  ∀ (n : ℕ) (σ : List ℕ) (x : ℕ), Legal n σ → ∀ I ∈ (stack n σ).tail, x ∈ I →
    ∀ w : List ℕ, IsPermOf n w → (σ ++ [x]) <+: w → Contains w (beta 2)

/-- **Statement (C)**: a legal word of full length avoids `12453`. -/
def CompleteHyp : Prop :=
  ∀ (n : ℕ) (σ : List ℕ), Legal n σ → σ.length = n → Avoids σ (beta 2)

/-! ### Sanity checks

The running example of the paper, `π = 9,11,10,14,5,12,6,2,3,8,4,7,1,13,15`
(\eqref{eq:running-example}), written `0`-based (`runningExample`, from
`Av12453.TwoThreshold.Thresholds`), and its `d = 2` scan, tabulated in \cref{ex:full-state}.
Row `i` of that table is the prefix `runningExample.take i`; `k = 0` is the empty prefix,
which the table does not list.  Every check below is a kernel evaluation (`decide`), so it
adds no axiom. -/

set_option maxRecDepth 100000 in
/-- The `d = 2` scan of the running example is legal at every step. -/
example : Legal 15 runningExample := by decide

set_option maxRecDepth 100000 in
/-- The interval-stack column of \cref{ex:full-state}, `0`-based.  Rows `1`–`15` of the
table are the entries `k = 1, …, 15`. -/
example : (List.range 16).map (fun k => stack 15 (runningExample.take k)) =
    [[], [], [{11, 12, 13, 14}], [{11, 12, 13, 14}], [{11, 12}, {14}], [{11, 12}, {14}],
      [{12}, {14}], [{6, 7, 12}, {14}], [{6, 7, 12}, {14}], [{3, 6, 7, 12}, {14}],
      [{3, 6}, {12}, {14}], [{6}, {12}, {14}], [{12}, {14}], [{12}, {14}], [{14}], []] := by
  decide

set_option maxRecDepth 100000 in
/-- The state column `H_𝐩(L)` of \cref{ex:full-state}: the pair `(𝐩, L)` after each
prefix. -/
example : (List.range 16).map (fun k => (p 15 (runningExample.take k),
      L 15 (runningExample.take k))) =
    [((15, 0), []), ((8, 6), []), ((8, 1), [4]), ((8, 0), [4]), ((8, 0), [2, 1]),
      ((4, 3), [2, 1]), ((4, 3), [1, 1]), ((4, 0), [3, 1]), ((1, 2), [3, 1]),
      ((1, 0), [4, 1]), ((1, 0), [2, 1, 1]), ((1, 0), [1, 1, 1]), ((1, 0), [1, 1]),
      ((0, 0), [1, 1]), ((0, 0), [1]), ((0, 0), [])] := by
  decide

set_option maxRecDepth 10000 in
/-- **The all-moves identity of \cref{ex:full-state}**, the successors of the state
`H_{(1,2)}((3,1))` reached after the eighth letter:
`H_{(1,2)}((3,1)) = H_{(0,2)}((3,1)) + H_{(1,0)}((4,1)) + H_{(1,1)}((3,1))
 + 2 H_{(1,2)}((2,1)) + H_{(1,2)}((1,1,1))`. -/
example : H (1, 2) [3, 1] =
    H (0, 2) [3, 1] + H (1, 0) [4, 1] + H (1, 1) [3, 1]
      + 2 * H (1, 2) [2, 1] + H (1, 2) [1, 1, 1] := by decide

/-- The same identity, read off \eqref{eq:H} itself rather than from the kernel: `H_eq_cons`
at `𝐩 = (1,2)`, `ℓ₁ = 3`, `L' = (1)` produces exactly the five successors of
\cref{ex:full-state}. -/
example : H (1, 2) [3, 1] =
    H (0, 2) [3, 1] + H (1, 0) [4, 1] + H (1, 1) [3, 1]
      + 2 * H (1, 2) [2, 1] + H (1, 2) [1, 1, 1] := by
  rw [H_eq_cons (by norm_num) (1, 2) [1], H_endpoint_two_le (by norm_num)]
  simp [Finset.sum_range_succ]
  ring

set_option maxRecDepth 4000 in
/-- `|Av₃(12453)| = 6`: all six permutations of `{0,1,2}` avoid `12453`. -/
example : H (3, 0) [] = 6 := by decide

set_option maxRecDepth 40000 in
/-- `|Av₅(12453)| = 119` (the first term below `5! = 120`). -/
example : H (5, 0) [] = 119 := by decide

set_option maxRecDepth 400000 in
/-- The first terms `1, 1, 2, 6, 24, 119` of `|Av_n(12453)|`, the paper's
\eqref{eq:first-terms}. -/
example : (List.range 6).map (fun k => H (k, 0) []) = [1, 1, 2, 6, 24, 119] := by decide

set_option maxRecDepth 1000000 in
/-- One term further: `|Av₆(12453)| = 694`. -/
example : H (6, 0) [] = 694 := by decide

-- The first ten terms of `|Av_n(12453)|`, `n = 0, …, 9`
-- (`code/data/av12453_terms_0_300.txt`): the paper's \eqref{eq:first-terms}.  Evaluated by
-- the compiler rather than by the kernel; `#guard_msgs` fails the build if the output
-- changes, so this is a live check even though `#eval` itself proves nothing.
set_option linter.hashCommand false in
/-- info: [1, 1, 2, 6, 24, 119, 694, 4581, 33286, 260927] -/
#guard_msgs in
#eval (List.range 10).map (fun k => H (k, 0) [])

end TwoThreshold
end Av12453
