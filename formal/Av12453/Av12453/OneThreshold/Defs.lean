/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Av12453.Basic

/-!
# The one-threshold scan and the literal recurrence for `Av(1342)`

This file sets up the objects of Sections 2.1--2.3 of the paper
*Protected tails and polynomial-time enumeration of permutations avoiding a direct sum of an
increasing pattern and 231* for `d = 1`, where
`β₁ = ι₁ ⊕ 231 = 1342` (`0`-based `[0, 2, 3, 1]`, `Av12453.beta_one`), and states the four
main theorems of component 3a.  Values and positions are `0`-based throughout, as in
`Av12453.Basic`; the paper's values `1, …, n` are this file's `0, …, n-1`.

## The scan

A *prefix* is a list `σ : List ℕ` of letters read so far.  `unread n σ` is the set of values
not yet read, `m n σ` the least letter read (the paper's threshold `m`, with the virtual
value `n` for the empty prefix), and `p n σ` the number of unread values below `m` (the
paper's control `p`).  `step` performs one legal move of \cref{def:scan-state} on the
interval stack -- a new minimum is a *merger*, which adjoins the values between it and the
old threshold to the active head (\cref{lem:merger}), a value of the active head is a
*split* (\cref{lem:first-letter}), and a value of a deferred interval is illegal
(\cref{lem:legal-moves}(b)) -- and `stackOf`/`stack` iterate it along the prefix.
`layout_of_legal` below is the scan-state property of \cref{def:scan-state} (the paper's
\cref{lem:legal-moves}(a)).  The paper's faithfulness (\cref{def:faithful}) is not
formalized as such: this development uses the separation criterion of
\cref{lem:1342-separators} as its invariant instead, and derives the two consequences
that the counting argument needs.
`Legal n σ` is the paper's *legal word* and `stack n σ` its stack `S(σ)`; `L n σ` lists the
interval sizes.

## The recurrence

`W p L` is \eqref{eq:W}, \eqref{eq:W-endpoint}, \eqref{eq:W-boundary}, defined by recursion
on the measure `p + L.sum` (\eqref{eq:rho-scalar}, `rho_eq`) and characterized by the three
equations `W_eq_nil`, `W_eq_cons` and `W_endpoint`.

## Main definitions

* `IsWord`, `unread`, `m`, `below`, `p` : the scanned prefix and its control.
* `step`, `stackAux`, `stackOf`, `Legal`, `stack`, `L` : the interval stack of a prefix.
* `Layout` : the ordered-layout invariant \eqref{eq:ordered-layout} for `d = 1`.
* `Adjacent`, `Sep`, `DiffIntervals` : the vocabulary of \cref{lem:1342-separators}.
* `W`, `Eend`, `nz` : the one-threshold recurrence.
* `perms`, `avoiders`, `A` : the permutations of `{0, …, n-1}`, the `τ`-avoiding ones, and
  the number of `1342`-avoiders with a given prefix.

## Main results

* `layout_of_legal` : every legal prefix has the ordered layout.
* `A_succ`, `A_complete` : the prefix partition of the avoiders.
* `W_eq_nil`, `W_eq_cons`, `W_endpoint` : the defining equations of `W`.
* `L_succ_newMin_cons`, `L_succ_newMin_nil`, `L_succ_active` : the effect of one move on
  `(p, L)`.
* `sep_invariant`, `deferred_no_completion`, `legal_complete_avoids`, `A_eq_W` : the four
  theorems (A)--(D) of component 3a, proved in the sibling modules.
* `av1342_count` : `W n ∅` is the number of `1342`-avoiding permutations of `{0, …, n-1}`.
-/

namespace Av12453
namespace OneThreshold

variable {n : ℕ} {σ τ : List ℕ} {x u v : ℕ}

/-! ### Words, unread values, the threshold `m` -/

/-- `σ` is a *word* over the alphabet `{0, …, n-1}`. -/
def IsWord (n : ℕ) (σ : List ℕ) : Prop := σ.Nodup ∧ ∀ x ∈ σ, x < n

/-- The unread values after the prefix `σ` has been read. -/
def unread (n : ℕ) (σ : List ℕ) : Finset ℕ := Finset.range n \ σ.toFinset

@[simp] theorem mem_unread {y : ℕ} : y ∈ unread n σ ↔ y < n ∧ y ∉ σ := by
  simp [unread]

theorem unread_append_singleton : unread n (σ ++ [x]) = (unread n σ).erase x := by
  ext y
  simp only [mem_unread, Finset.mem_erase, List.mem_append, List.mem_singleton]
  tauto

/-- The current minimum `m`: the least letter of `σ`, and the virtual value `n` for the
empty prefix. -/
def m (n : ℕ) (σ : List ℕ) : ℕ := σ.foldl min n

@[simp] theorem m_nil : m n [] = n := rfl

theorem m_cons {y : ℕ} : m n (y :: σ) = m (min n y) σ := rfl

theorem m_append_singleton : m n (σ ++ [x]) = min (m n σ) x := by
  simp [m, List.foldl_append]

theorem m_le (n : ℕ) (σ : List ℕ) : m n σ ≤ n := by
  induction σ generalizing n with
  | nil => exact le_rfl
  | cons y t ih => exact (ih (min n y)).trans (min_le_left _ _)

theorem m_le_of_mem {y : ℕ} (hy : y ∈ σ) : m n σ ≤ y := by
  induction σ generalizing n with
  | nil => simp at hy
  | cons z t ih =>
    rcases List.mem_cons.mp hy with rfl | h
    · rw [m_cons]; exact (m_le _ _).trans (min_le_right _ _)
    · rw [m_cons]; exact ih h

theorem m_mem_or_eq : m n σ ∈ σ ∨ m n σ = n := by
  induction σ generalizing n with
  | nil => exact Or.inr rfl
  | cons y t ih =>
    rw [m_cons]
    rcases ih (n := min n y) with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases min_cases n y with ⟨he, _⟩ | ⟨he, _⟩
      · exact Or.inr (h.trans he)
      · refine Or.inl ?_
        rw [h, he]
        simp

/-- For a nonempty word the threshold is one of its letters. -/
theorem m_mem (hw : IsWord n σ) (hne : σ ≠ []) : m n σ ∈ σ := by
  rcases m_mem_or_eq (n := n) (σ := σ) with h | h
  · exact h
  · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil σ hne
    exact absurd ((h ▸ m_le_of_mem hy : n ≤ y).trans_lt (hw.2 y hy)) (lt_irrefl n)

/-- The threshold of a word has been read; for the empty word it is out of range. -/
theorem m_not_unread (hw : IsWord n σ) : m n σ ∉ unread n σ := by
  rcases eq_or_ne σ [] with rfl | hne
  · simp
  · simp only [mem_unread, not_and, not_not]
    exact fun _ => m_mem hw hne

/-! ### The control `p` -/

/-- The number of unread values strictly below `x`. -/
def below (n : ℕ) (σ : List ℕ) (x : ℕ) : ℕ := ((unread n σ).filter (· < x)).card

/-- The control `p`: the number of unread values below the threshold `m`. -/
def p (n : ℕ) (σ : List ℕ) : ℕ := below n σ (m n σ)

@[simp] theorem p_nil : p n [] = n := by
  simp only [p, below, m_nil, unread, List.toFinset_nil, Finset.sdiff_empty]
  rw [Finset.filter_true_of_mem (by simp)]
  simp

/-! ### The interval stack -/

/-- Delete the empty intervals from a list of intervals. -/
def nzI (st : List (Finset ℕ)) : List (Finset ℕ) := st.filter (fun I => decide (I.card ≠ 0))

theorem mem_nzI {st : List (Finset ℕ)} {I : Finset ℕ} : I ∈ nzI st ↔ I ∈ st ∧ I.Nonempty := by
  simp only [nzI, List.mem_filter, decide_eq_true_eq, ne_eq, Finset.card_eq_zero,
    ← Finset.nonempty_iff_ne_empty]

theorem nzI_sublist (st : List (Finset ℕ)) : List.Sublist (nzI st) st := List.filter_sublist

/-- Delete the zero entries of a composition (the paper's `nz`). -/
def nz (L : List ℕ) : List ℕ := L.filter (fun a => decide (a ≠ 0))

@[simp] theorem nz_nil : nz [] = [] := rfl

theorem nz_singleton (a : ℕ) : nz [a] = if a = 0 then [] else [a] := by
  by_cases h : a = 0 <;> simp [nz, h]

@[simp] theorem nz_singleton_sum (a : ℕ) : (nz [a]).sum = a := by
  rw [nz_singleton]; by_cases h : a = 0 <;> simp [h]

theorem map_card_nzI (st : List (Finset ℕ)) :
    (nzI st).map Finset.card = nz (st.map Finset.card) := by
  induction st with
  | nil => rfl
  | cons I t ih =>
    simp only [nzI, nz] at ih ⊢
    rw [List.map_cons]
    by_cases h : I.card = 0
    · rw [List.filter_cons_of_neg (by simp [h]), List.filter_cons_of_neg (by simp [h]), ih]
    · rw [List.filter_cons_of_pos (by simp [h]), List.filter_cons_of_pos (by simp [h]),
        List.map_cons, ih]

/-- One move of the one-threshold scan.  `σ` is the prefix read so far, `st` its interval
stack, and `x` the next letter; `none` marks an illegal move. -/
def step (n : ℕ) (σ : List ℕ) (st : List (Finset ℕ)) (x : ℕ) : Option (List (Finset ℕ)) :=
  if x ∈ unread n σ then
    if x < m n σ then
      match st with
      | I₁ :: tail => some (((unread n σ).filter (fun y => x < y ∧ y < m n σ) ∪ I₁) :: tail)
      | [] => some (nzI [(unread n σ).filter (fun y => x < y ∧ y < m n σ)])
    else
      match st with
      | I₁ :: tail =>
          if x ∈ I₁ then
            some (nzI [I₁.filter (· < x), I₁.filter (fun y => x < y)] ++ tail)
          else none
      | [] => none
  else none

/-- The values adjoined to the active head by the new minimum `x` (the `E` of the merger
lemma). -/
def mergeSet (n : ℕ) (σ : List ℕ) (x : ℕ) : Finset ℕ :=
  (unread n σ).filter (fun y => x < y ∧ y < m n σ)

theorem mem_mergeSet {y : ℕ} :
    y ∈ mergeSet n σ x ↔ (y ∈ unread n σ ∧ x < y ∧ y < m n σ) := by
  simp only [mergeSet, Finset.mem_filter]

theorem step_of_not_unread {st : List (Finset ℕ)} (hx : x ∉ unread n σ) :
    step n σ st x = none := by
  simp [step, hx]

theorem step_newMin_cons {I₁ : Finset ℕ} {tail : List (Finset ℕ)} (hx : x ∈ unread n σ)
    (hlt : x < m n σ) :
    step n σ (I₁ :: tail) x = some ((mergeSet n σ x ∪ I₁) :: tail) := by
  simp [step, hx, hlt, mergeSet]

theorem step_newMin_nil (hx : x ∈ unread n σ) (hlt : x < m n σ) :
    step n σ [] x = some (nzI [mergeSet n σ x]) := by
  simp [step, hx, hlt, mergeSet]

theorem step_active {I₁ : Finset ℕ} {tail : List (Finset ℕ)} (hx : x ∈ unread n σ)
    (hge : ¬ x < m n σ) (hmem : x ∈ I₁) :
    step n σ (I₁ :: tail) x =
      some (nzI [I₁.filter (· < x), I₁.filter (fun y => x < y)] ++ tail) := by
  simp [step, hx, hge, hmem]

theorem step_deferred {I₁ : Finset ℕ} {tail : List (Finset ℕ)} (hge : ¬ x < m n σ)
    (hmem : x ∉ I₁) : step n σ (I₁ :: tail) x = none := by
  by_cases hx : x ∈ unread n σ <;> simp [step, hx, hge, hmem]

theorem step_empty_stack (hge : ¬ x < m n σ) : step n σ [] x = none := by
  by_cases hx : x ∈ unread n σ <;> simp [step, hx, hge]

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

/-- Every letter of a legal prefix is an unread value at the moment it is read. -/
theorem Legal.isWord (h : Legal n σ) : IsWord n σ := by
  induction σ using List.reverseRecOn with
  | nil => exact ⟨List.nodup_nil, by simp⟩
  | append_singleton t y ih =>
    have ht := h.of_append_singleton
    obtain ⟨hnd, hlt⟩ := ih ht
    have hy : y ∈ unread n t := by
      refine unread_of_step_isSome (st := stack n t) ?_
      rw [stack_succ ht h]; rfl
    rw [mem_unread] at hy
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

theorem Legal.mem_unread (h : Legal n (σ ++ [x])) : x ∈ unread n σ :=
  unread_of_step_isSome (st := stack n σ)
    (by rw [stack_succ h.of_append_singleton h]; rfl)


/-! ### The one-threshold recurrence `W`

The recurrence is the paper's \eqref{eq:W}, \eqref{eq:W-endpoint} and \eqref{eq:W-boundary}.
It is defined here by recursion on the fuel `k`, with `W p L` evaluating the body with
`k = p + L.sum + 1`; `Waux_congr` shows that any sufficient amount of fuel gives the same
value, and `W_eq_nil`, `W_eq_cons` and `W_endpoint` are the three defining equations.  On a
list with a zero entry -- a state that never occurs along the scan, since the intervals of
the stack are nonempty -- `W` is `0`. -/

/-- Fuel-driven evaluation of the one-threshold recurrence. -/
private def Waux : ℕ → ℕ → List ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, q, [] => (if q = 0 then 1 else 0) + ∑ h ∈ Finset.range q, Waux k h (nz [q - 1 - h])
  | _ + 1, _, 0 :: _ => 0
  | k + 1, q, (ℓ + 1) :: L' =>
      (∑ h ∈ Finset.range q, Waux k h ((ℓ + 1 + q - 1 - h) :: L'))
        + (if ℓ = 0 then Waux k q L' else 2 * Waux k q (ℓ :: L'))
        + ∑ a ∈ Finset.Ico 1 ℓ, Waux k q (a :: (ℓ - a) :: L')

private theorem Waux_nil (k q : ℕ) :
    Waux (k + 1) q [] =
      (if q = 0 then 1 else 0) + ∑ h ∈ Finset.range q, Waux k h (nz [q - 1 - h]) := rfl

private theorem Waux_zero (k q : ℕ) (L' : List ℕ) : Waux (k + 1) q (0 :: L') = 0 := rfl

private theorem Waux_cons (k q ℓ : ℕ) (L' : List ℕ) :
    Waux (k + 1) q ((ℓ + 1) :: L') =
      (∑ h ∈ Finset.range q, Waux k h ((ℓ + 1 + q - 1 - h) :: L'))
        + (if ℓ = 0 then Waux k q L' else 2 * Waux k q (ℓ :: L'))
        + ∑ a ∈ Finset.Ico 1 ℓ, Waux k q (a :: (ℓ - a) :: L') := rfl

/-- Any two amounts of fuel exceeding the measure `q + L.sum` give the same value. -/
private theorem Waux_congr : ∀ k k' q (l : List ℕ),
    q + l.sum < k → q + l.sum < k' → Waux k q l = Waux k' q l := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro k' q l h1 h2
    obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
    obtain ⟨k1, rfl⟩ : ∃ k1, k' = k1 + 1 := ⟨k' - 1, by omega⟩
    match l with
    | [] =>
      rw [Waux_nil, Waux_nil]
      refine congrArg _ (Finset.sum_congr rfl fun h hh => ?_)
      rw [Finset.mem_range] at hh
      simp only [List.sum_nil, add_zero] at h1 h2
      exact ih k0 (by omega) k1 h (nz [q - 1 - h]) (by simp; omega) (by simp; omega)
    | 0 :: L' => rw [Waux_zero, Waux_zero]
    | (ℓ + 1) :: L' =>
      simp only [List.sum_cons] at h1 h2
      rw [Waux_cons, Waux_cons]
      have e1 : ∀ h ∈ Finset.range q,
          Waux k0 h ((ℓ + 1 + q - 1 - h) :: L') = Waux k1 h ((ℓ + 1 + q - 1 - h) :: L') := by
        intro h hh
        rw [Finset.mem_range] at hh
        exact ih k0 (by omega) k1 h _ (by simp; omega) (by simp; omega)
      have e2 : ∀ a ∈ Finset.Ico 1 ℓ,
          Waux k0 q (a :: (ℓ - a) :: L') = Waux k1 q (a :: (ℓ - a) :: L') := by
        intro a ha
        rw [Finset.mem_Ico] at ha
        exact ih k0 (by omega) k1 q _ (by simp; omega) (by simp; omega)
      have e3 : Waux k0 q L' = Waux k1 q L' :=
        ih k0 (by omega) k1 q L' (by omega) (by omega)
      have e4 : Waux k0 q (ℓ :: L') = Waux k1 q (ℓ :: L') :=
        ih k0 (by omega) k1 q _ (by simp; omega) (by simp; omega)
      rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, e3, e4]

/--
`W p L` is the paper's `W_p(L)`: the number of `1342`-avoiding completions of a scanned
prefix whose control is `p` and whose interval sizes are `L`.
-/
def W (q : ℕ) (l : List ℕ) : ℕ := Waux (q + l.sum + 1) q l

private theorem W_eq_Waux {q : ℕ} {l : List ℕ} {k : ℕ} (hk : q + l.sum < k) :
    W q l = Waux k q l :=
  Waux_congr _ _ _ _ (by omega) hk

/-- The paper's `E_ℓ(p, L')` of \eqref{eq:W-endpoint}. -/
def Eend (ℓ q : ℕ) (L' : List ℕ) : ℕ :=
  if ℓ = 1 then W q L' else 2 * W q ((ℓ - 1) :: L')

/-- **\eqref{eq:W-endpoint}**: the endpoint term. -/
theorem W_endpoint (ℓ q : ℕ) (L' : List ℕ) :
    Eend ℓ q L' = if ℓ = 1 then W q L' else 2 * W q ((ℓ - 1) :: L') := rfl

theorem W_endpoint_one (q : ℕ) (L' : List ℕ) : Eend 1 q L' = W q L' := by
  simp [Eend]

theorem W_endpoint_two_le {ℓ : ℕ} (h : 2 ≤ ℓ) (q : ℕ) (L' : List ℕ) :
    Eend ℓ q L' = 2 * W q ((ℓ - 1) :: L') := by
  rw [Eend, if_neg (by omega)]

/-- **\eqref{eq:W-boundary}**: the empty stack. -/
theorem W_eq_nil (q : ℕ) :
    W q [] = (if q = 0 then 1 else 0) + ∑ h ∈ Finset.range q, W h (nz [q - 1 - h]) := by
  rw [W, List.sum_nil, Nat.add_zero, Waux_nil]
  refine congrArg _ (Finset.sum_congr rfl fun h hh => ?_)
  rw [Finset.mem_range] at hh
  exact (W_eq_Waux (by simp; omega)).symm

/-- **\eqref{eq:W}**: the recurrence at a nonempty stack with active head of size `ℓ ≥ 1`. -/
theorem W_eq_cons {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (q : ℕ) (L' : List ℕ) :
    W q (ℓ :: L') =
      (∑ h ∈ Finset.range q, W h ((ℓ + q - 1 - h) :: L'))
        + Eend ℓ q L'
        + ∑ a ∈ Finset.Ico 1 (ℓ - 1), W q (a :: (ℓ - 1 - a) :: L') := by
  obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
  rw [W, List.sum_cons, show q + (j + 1 + L'.sum) + 1 = (q + j + L'.sum + 1) + 1 by omega,
    Waux_cons]
  have e1 : ∀ h ∈ Finset.range q,
      Waux (q + j + L'.sum + 1) h ((j + 1 + q - 1 - h) :: L') =
        W h ((j + 1 + q - 1 - h) :: L') := by
    intro h hh
    rw [Finset.mem_range] at hh
    exact (W_eq_Waux (by simp; omega)).symm
  have e2 : ∀ a ∈ Finset.Ico 1 j,
      Waux (q + j + L'.sum + 1) q (a :: (j - a) :: L') = W q (a :: (j - a) :: L') := by
    intro a ha
    rw [Finset.mem_Ico] at ha
    exact (W_eq_Waux (by simp; omega)).symm
  have hE : (if j = 0 then Waux (q + j + L'.sum + 1) q L'
        else 2 * Waux (q + j + L'.sum + 1) q (j :: L')) = Eend (j + 1) q L' := by
    rw [Eend]
    by_cases hj : j = 0
    · subst hj
      rw [if_pos rfl, if_pos rfl]
      exact (W_eq_Waux (by omega)).symm
    · rw [if_neg hj, if_neg (show ¬ (j + 1 = 1) by omega), Nat.add_sub_cancel]
      exact congrArg _ (W_eq_Waux (by simp; omega)).symm
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, hE, Nat.add_sub_cancel]

/-- A state with an empty interval is unreachable, and gets the value `0`. -/
theorem W_zero_head (q : ℕ) (L' : List ℕ) : W q (0 :: L') = 0 := by
  rw [W, List.sum_cons, Nat.zero_add]
  cases h : q + L'.sum with
  | zero => rw [Waux_zero]
  | succ k => rw [Waux_zero]

/-! ### Decidability of containment

These instances make `A` and `avoiders` computable; they are also what the `decide` sanity
checks at the end of the file use. -/

theorem orderIso_iff_getD (u v : List ℕ) :
    OrderIso u v ↔ u.length = v.length ∧
      ∀ i < u.length, ∀ j < u.length,
        (u.getD i 0 < u.getD j 0 ↔ v.getD i 0 < v.getD j 0) := by
  constructor
  · rintro ⟨hlen, hiso⟩
    refine ⟨hlen, fun i hi j hj => ?_⟩
    have hiv : i < v.length := hlen ▸ hi
    have hjv : j < v.length := hlen ▸ hj
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj,
      List.getD_eq_getElem _ _ hiv, List.getD_eq_getElem _ _ hjv]
    exact hiso i j hi hj hiv hjv
  · rintro ⟨hlen, hiso⟩
    refine ⟨hlen, fun i j hiu hju hiv hjv => ?_⟩
    have h := hiso i hiu j hju
    rwa [List.getD_eq_getElem _ _ hiu, List.getD_eq_getElem _ _ hju,
      List.getD_eq_getElem _ _ hiv, List.getD_eq_getElem _ _ hjv] at h

instance decidableOrderIso (u v : List ℕ) : Decidable (OrderIso u v) :=
  decidable_of_iff _ (orderIso_iff_getD u v).symm

theorem contains_iff_sublists (w τ : List ℕ) : Contains w τ ↔ ∃ s ∈ w.sublists, OrderIso s τ := by
  simp only [Contains, List.mem_sublists]

instance decidableContains (w τ : List ℕ) : Decidable (Contains w τ) :=
  decidable_of_iff _ (contains_iff_sublists w τ).symm

instance decidableAvoids (w τ : List ℕ) : Decidable (Avoids w τ) :=
  decidable_of_iff _ (avoids_iff (w := w) (τ := τ)).symm

/-! ### Counting avoiders with a given prefix -/

/-- The permutations of `{0, …, n-1}`, written as words. -/
def perms (n : ℕ) : Finset (List ℕ) := (List.range n).permutations.toFinset

@[simp] theorem mem_perms {w : List ℕ} : w ∈ perms n ↔ IsPermOf n w := by
  simp [perms, IsPermOf, List.mem_permutations]

/-- The `τ`-avoiding permutations of `{0, …, n-1}`. -/
def avoiders (n : ℕ) (τ : List ℕ) : Finset (List ℕ) := (perms n).filter fun w => Avoids w τ

/-- `A n σ` is the number of `1342`-avoiding permutations of `{0, …, n-1}` that begin with
the prefix `σ`. -/
def A (n : ℕ) (σ : List ℕ) : ℕ :=
  ((perms n).filter fun w => σ <+: w ∧ Avoids w (beta 1)).card

theorem A_nil (n : ℕ) : A n [] = (avoiders n (beta 1)).card := by
  rw [A, avoiders]
  exact congrArg _ (Finset.filter_congr fun w _ => by simp)

theorem isPermOf_of_isWord (hw : IsWord n σ) (hlen : σ.length = n) : IsPermOf n σ :=
  (List.subperm_of_subset hw.1 fun y hy => List.mem_range.mpr (hw.2 y hy)).perm_of_length_le
    (by simp [hlen])

theorem take_succ_eq {w : List ℕ} {k : ℕ} (h : k < w.length) :
    w.take (k + 1) = w.take k ++ [w.getD k 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem _ _ h]
  rfl

/-- Reading one more letter: `σ ++ [x]` is a prefix of `w` exactly when `σ` is and the
letter of `w` in position `σ.length` is `x`. -/
theorem prefix_append_singleton_iff {w : List ℕ} (hlen : σ.length < w.length) :
    (σ ++ [x]) <+: w ↔ (σ <+: w ∧ w.getD σ.length 0 = x) := by
  constructor
  · intro h
    have hp : σ <+: w := (List.prefix_append σ [x]).trans h
    refine ⟨hp, ?_⟩
    have h1 : σ ++ [x] = w.take (σ.length + 1) := by
      simpa using List.prefix_iff_eq_take.mp h
    rw [take_succ_eq hlen, ← List.prefix_iff_eq_take.mp hp] at h1
    simpa using (List.append_cancel_left h1).symm
  · rintro ⟨hp, rfl⟩
    have h1 : σ ++ [w.getD σ.length 0] = w.take (σ.length + 1) := by
      rw [take_succ_eq hlen, ← List.prefix_iff_eq_take.mp hp]
    rw [h1]
    exact List.take_prefix _ _

/-- The letter read at position `σ.length` is one of the unread values. -/
theorem getD_mem_unread {w : List ℕ} (hw : IsPermOf n w) (hp : σ <+: w) (hlen : σ.length < n) :
    w.getD σ.length 0 ∈ unread n σ := by
  have hwl : w.length = n := hw.length
  have hlt : σ.length < w.length := by omega
  have hmemw : w.getD σ.length 0 ∈ w := by
    rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem _
  refine mem_unread.mpr ⟨by simpa using hw.mem_iff.mp hmemw, ?_⟩
  intro hmem
  have hsplit : (w.take σ.length ++ w.drop σ.length).Nodup := by
    rw [List.take_append_drop]; exact hw.nodup
  rw [List.nodup_append] at hsplit
  have hσ : σ = w.take σ.length := List.prefix_iff_eq_take.mp hp
  have hmemdrop : w.getD σ.length 0 ∈ w.drop σ.length := by
    rw [List.getD_eq_getElem _ _ hlt]
    have h0 : w[σ.length] = (w.drop σ.length)[0]'(by simp; omega) := by
      simp [List.getElem_drop]
    rw [h0]
    exact List.getElem_mem _
  exact hsplit.2.2 _ (hσ ▸ hmem) _ hmemdrop rfl

/-- **The prefix partition.**  With at least one letter left to read, the avoiders with
prefix `σ` are partitioned by their next letter, which ranges over the unread values. -/
theorem A_succ (n : ℕ) (σ : List ℕ) (hlen : σ.length < n) :
    A n σ = ∑ x ∈ unread n σ, A n (σ ++ [x]) := by
  have hmaps : ∀ w ∈ (perms n).filter fun w => σ <+: w ∧ Avoids w (beta 1),
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
    A n σ = if Avoids σ (beta 1) then 1 else 0 := by
  have hperm : IsPermOf n σ := isPermOf_of_isWord hw hlen
  have hset : ((perms n).filter fun w => σ <+: w ∧ Avoids w (beta 1))
      = if Avoids σ (beta 1) then {σ} else ∅ := by
    ext w
    rw [Finset.mem_filter, mem_perms]
    by_cases hav : Avoids σ (beta 1)
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
  by_cases hav : Avoids σ (beta 1) <;> simp [hav]

/-! ### The ordered layout -/

/-- The union of the intervals of a stack. -/
def stackUnion (st : List (Finset ℕ)) : Finset ℕ := st.foldr (· ∪ ·) ∅

@[simp] theorem mem_stackUnion {st : List (Finset ℕ)} {y : ℕ} :
    y ∈ stackUnion st ↔ ∃ I ∈ st, y ∈ I := by
  induction st with
  | nil => simp [stackUnion]
  | cons I t ih =>
    simp only [stackUnion, List.foldr_cons, Finset.mem_union, List.mem_cons] at *
    rw [ih]
    constructor
    · rintro (h | ⟨J, hJ, hyJ⟩)
      · exact ⟨I, Or.inl rfl, h⟩
      · exact ⟨J, Or.inr hJ, hyJ⟩
    · rintro ⟨J, rfl | hJ, hyJ⟩
      · exact Or.inl hyJ
      · exact Or.inr ⟨J, hJ, hyJ⟩

@[simp] theorem stackUnion_cons (I : Finset ℕ) (st : List (Finset ℕ)) :
    stackUnion (I :: st) = I ∪ stackUnion st := rfl

theorem stackUnion_append (s t : List (Finset ℕ)) :
    stackUnion (s ++ t) = stackUnion s ∪ stackUnion t := by
  induction s with
  | nil => simp [stackUnion]
  | cons I r ih => rw [List.cons_append, stackUnion_cons, stackUnion_cons, ih, Finset.union_assoc]

theorem stackUnion_nzI (st : List (Finset ℕ)) : stackUnion (nzI st) = stackUnion st := by
  ext y
  simp only [mem_stackUnion, mem_nzI]
  constructor
  · rintro ⟨I, ⟨hI, -⟩, hy⟩; exact ⟨I, hI, hy⟩
  · rintro ⟨I, hI, hy⟩; exact ⟨I, ⟨hI, ⟨y, hy⟩⟩, hy⟩

/--
**The layout invariant** for `d = 1`, the paper's \eqref{eq:ordered-layout} together with
the run condition of \cref{sec:stack}: the intervals of the stack are nonempty, increasing,
their union is the set of unread values above the threshold `m`, and each of them is a run
of the unread values.
-/
structure Layout (n : ℕ) (σ : List ℕ) : Prop where
  /-- Every interval of the stack is nonempty. -/
  nonempty : ∀ I ∈ stack n σ, I.Nonempty
  /-- The intervals increase: `I₁ < I₂ < ⋯` elementwise. -/
  ordered : (stack n σ).Pairwise fun I J => ∀ a ∈ I, ∀ b ∈ J, a < b
  /-- The union of the intervals is the set of unread values above `m`. -/
  union : stackUnion (stack n σ) = (unread n σ).filter fun y => m n σ < y
  /-- Each interval is a run of the unread values. -/
  runs : ∀ I ∈ stack n σ, ∀ a ∈ I, ∀ b ∈ I, ∀ y ∈ unread n σ, a < y → y < b → y ∈ I

theorem Layout.mem_iff (h : Layout n σ) {y : ℕ} :
    (∃ I ∈ stack n σ, y ∈ I) ↔ (y ∈ unread n σ ∧ m n σ < y) := by
  rw [← mem_stackUnion, h.union, Finset.mem_filter]

theorem Layout.unread_of_mem (h : Layout n σ) {I : Finset ℕ} (hI : I ∈ stack n σ) {a : ℕ}
    (ha : a ∈ I) : a ∈ unread n σ := (h.mem_iff.mp ⟨I, hI, ha⟩).1

theorem Layout.lt_of_mem (h : Layout n σ) {I : Finset ℕ} (hI : I ∈ stack n σ) {a : ℕ}
    (ha : a ∈ I) : m n σ < a := (h.mem_iff.mp ⟨I, hI, ha⟩).2

theorem Layout.exists_mem (h : Layout n σ) {y : ℕ} (hy : y ∈ unread n σ) (hm : m n σ < y) :
    ∃ I ∈ stack n σ, y ∈ I := h.mem_iff.mpr ⟨hy, hm⟩

/-- The active head is an initial segment of the unread values above `m`. -/
theorem Layout.head_initial (h : Layout n σ) {I₁ : Finset ℕ} {tail : List (Finset ℕ)}
    (hst : stack n σ = I₁ :: tail) {y b : ℕ} (hy : y ∈ unread n σ) (hm : m n σ < y)
    (hb : b ∈ I₁) (hyb : y < b) : y ∈ I₁ := by
  obtain ⟨J, hJ, hyJ⟩ := h.exists_mem hy hm
  rw [hst, List.mem_cons] at hJ
  rcases hJ with rfl | hJ
  · exact hyJ
  · have hpw := h.ordered
    rw [hst, List.pairwise_cons] at hpw
    exact absurd (hpw.1 J hJ b hb y hyJ) (by omega)

/-! ### Adjacency and separations -/

/-- Two unread values are *adjacent* when no unread value lies strictly between them. -/
def Adjacent (n : ℕ) (σ : List ℕ) (u v : ℕ) : Prop :=
  u ∈ unread n σ ∧ v ∈ unread n σ ∧ u < v ∧ ∀ y ∈ unread n σ, ¬(u < y ∧ y < v)

set_option linter.unusedVariables false in
/--
The separation predicate of \cref{lem:1342-separators} and \cref{cor:separators}(ii): some
letter `z` with `u < z < v` was read after a letter `c < u`.  For `d = 1` every read letter
is a trigger, which is why `c` ranges over all read letters.
-/
def Sep (n : ℕ) (σ : List ℕ) (u v : ℕ) : Prop :=
  ∃ c z, c ∈ σ ∧ z ∈ σ ∧ σ.idxOf c < σ.idxOf z ∧ c < u ∧ u < z ∧ z < v

/-- `u` and `v` lie in different intervals of the stack: \cref{cor:separators}(i). -/
def DiffIntervals (n : ℕ) (σ : List ℕ) (u v : ℕ) : Prop :=
  ¬ ∃ I ∈ stack n σ, u ∈ I ∧ v ∈ I

/-! ### The transition of `(p, L)` -/

theorem card_filter_lt_add_card_filter_gt {S : Finset ℕ} {y : ℕ} (hy : y ∈ S) :
    (S.filter (· < y)).card + 1 + (S.filter fun z => y < z).card = S.card := by
  have h1 : S = (S.filter (· < y)) ∪ insert y (S.filter fun z => y < z) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_insert]
    constructor
    · intro hz
      rcases lt_trichotomy z y with h | h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨hz, h⟩)
    · rintro (⟨hz, -⟩ | rfl | ⟨hz, -⟩) <;> assumption
  have hdisj : Disjoint (S.filter (· < y)) (insert y (S.filter fun z => y < z)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_filter] at ha
    simp only [Finset.mem_insert, Finset.mem_filter] at hb
    rcases hb with rfl | ⟨-, h⟩ <;> omega
  have hnot : y ∉ S.filter fun z => y < z := by simp
  conv_rhs => rw [h1]
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_insert_of_notMem hnot]
  omega

theorem rank_lt_card {S : Finset ℕ} {x : ℕ} (hx : x ∈ S) :
    (S.filter (· < x)).card < S.card := by
  have hsub : S.filter (· < x) ⊆ S.erase x := by
    intro y hy
    rw [Finset.mem_filter] at hy
    exact Finset.mem_erase.mpr ⟨by omega, hy.1⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hx] at h1
  have h2 := Finset.card_pos.mpr ⟨x, hx⟩
  omega

theorem rank_inj {S : Finset ℕ} {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S)
    (hab : (S.filter (· < a)).card = (S.filter (· < b)).card) : a = b := by
  by_contra hne
  have key : ∀ c ∈ S, ∀ d ∈ S, c < d →
      (S.filter (· < c)).card < (S.filter (· < d)).card := by
    intro c hc d hd hcd
    refine Finset.card_lt_card ⟨?_, ?_⟩
    · intro y hy
      rw [Finset.mem_filter] at hy ⊢
      exact ⟨hy.1, by omega⟩
    · intro hsub
      have := hsub (Finset.mem_filter.mpr ⟨hc, hcd⟩)
      rw [Finset.mem_filter] at this
      omega
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd hab (by have := key a ha b hb h; omega)
  · exact absurd hab (by have := key b hb a ha h; omega)

/-- **Reindexing by local rank.**  The map sending a value of `S` to the number of values of
`S` below it is a bijection from `S` onto `{0, …, |S| - 1}`. -/
theorem sum_rank_eq {M : Type*} [AddCommMonoid M] (S : Finset ℕ) (f : ℕ → M) :
    ∑ x ∈ S, f ((S.filter (· < x)).card) = ∑ h ∈ Finset.range S.card, f h := by
  have hinj : ∀ a ∈ S, ∀ b ∈ S, (S.filter (· < a)).card = (S.filter (· < b)).card → a = b :=
    fun a ha b hb hab => rank_inj ha hb hab
  rw [← Finset.sum_image hinj]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨x, hx, rfl⟩ := hk
    exact Finset.mem_range.mpr (rank_lt_card hx)
  · rw [Finset.card_range, Finset.card_image_of_injOn (fun a ha b hb hab => hinj a ha b hb hab)]

theorem filter_filter_lt_of_lt (hlt : x < m n σ) :
    ((unread n σ).filter (· < m n σ)).filter (· < x) = (unread n σ).filter (· < x) := by
  refine Finset.ext fun y => ?_
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hy, -⟩, h2⟩; exact ⟨hy, h2⟩
  · rintro ⟨hy, h2⟩; exact ⟨⟨hy, by omega⟩, h2⟩

/-- **The new minima are indexed by `h = 0, …, p-1`**: the first line of \eqref{eq:W}.  The
unread values below the threshold, listed by the number `h` of unread values below them, run
through `0, …, p-1`. -/
theorem sum_below_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ x ∈ (unread n σ).filter (· < m n σ), f (below n σ x)
      = ∑ h ∈ Finset.range (p n σ), f h := by
  have hp : p n σ = ((unread n σ).filter (· < m n σ)).card := rfl
  rw [hp, ← sum_rank_eq]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mem_filter] at hx
  rw [below, ← filter_filter_lt_of_lt hx.2]

theorem m_succ_newMin (hlt : x < m n σ) : m n (σ ++ [x]) = x := by
  rw [m_append_singleton]; omega

theorem m_succ_active (hge : m n σ ≤ x) : m n (σ ++ [x]) = m n σ := by
  rw [m_append_singleton]; omega

theorem p_succ_newMin (hlt : x < m n σ) : p n (σ ++ [x]) = below n σ x := by
  rw [p, m_succ_newMin hlt, below, below, unread_append_singleton]
  refine congrArg _ (Finset.ext fun y => ?_)
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨-, hy⟩, h⟩; exact ⟨hy, h⟩
  · rintro ⟨hy, h⟩; exact ⟨⟨by omega, hy⟩, h⟩

theorem p_succ_active (hge : m n σ ≤ x) : p n (σ ++ [x]) = p n σ := by
  rw [p, p, m_succ_active hge, below, below, unread_append_singleton]
  refine congrArg _ (Finset.ext fun y => ?_)
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨-, hy⟩, h⟩; exact ⟨hy, h⟩
  · rintro ⟨hy, h⟩; exact ⟨⟨by omega, hy⟩, h⟩

/-- The merger set has `p - 1 - h` values, where `h` is the number of unread values below
the new minimum. -/
theorem card_mergeSet (hx : x ∈ unread n σ) (hlt : x < m n σ) :
    below n σ x + 1 + (mergeSet n σ x).card = p n σ := by
  have hxS : x ∈ (unread n σ).filter (· < m n σ) := Finset.mem_filter.mpr ⟨hx, hlt⟩
  have h := card_filter_lt_add_card_filter_gt hxS
  rw [Finset.filter_filter, Finset.filter_filter] at h
  have e1 : (unread n σ).filter (fun y => y < m n σ ∧ y < x) = (unread n σ).filter (· < x) := by
    refine Finset.ext fun y => ?_
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hy, -, h2⟩; exact ⟨hy, h2⟩
    · rintro ⟨hy, h2⟩; exact ⟨hy, by omega, h2⟩
  have e2 : (unread n σ).filter (fun y => y < m n σ ∧ x < y) = mergeSet n σ x := by
    refine Finset.ext fun y => ?_
    simp only [Finset.mem_filter, mergeSet]
    tauto
  rw [e1, e2] at h
  exact h

theorem legal_succ_of_newMin_cons (hleg : Legal n σ) {I₁ : Finset ℕ} {tail : List (Finset ℕ)}
    (hst : stack n σ = I₁ :: tail) (hx : x ∈ unread n σ) (hlt : x < m n σ) :
    Legal n (σ ++ [x]) ∧ stack n (σ ++ [x]) = (mergeSet n σ x ∪ I₁) :: tail := by
  have h : stackOf n (σ ++ [x]) = some ((mergeSet n σ x ∪ I₁) :: tail) := by
    rw [stackOf_succ hleg, hst, step_newMin_cons hx hlt]
  exact ⟨by rw [Legal, h]; rfl, by rw [stack, h]; rfl⟩

theorem legal_succ_of_newMin_nil (hleg : Legal n σ) (hst : stack n σ = [])
    (hx : x ∈ unread n σ) (hlt : x < m n σ) :
    Legal n (σ ++ [x]) ∧ stack n (σ ++ [x]) = nzI [mergeSet n σ x] := by
  have h : stackOf n (σ ++ [x]) = some (nzI [mergeSet n σ x]) := by
    rw [stackOf_succ hleg, hst, step_newMin_nil hx hlt]
  exact ⟨by rw [Legal, h]; rfl, by rw [stack, h]; rfl⟩

theorem legal_succ_of_active (hleg : Legal n σ) {I₁ : Finset ℕ} {tail : List (Finset ℕ)}
    (hst : stack n σ = I₁ :: tail) (hx : x ∈ unread n σ) (hge : ¬ x < m n σ) (hmem : x ∈ I₁) :
    Legal n (σ ++ [x]) ∧
      stack n (σ ++ [x]) = nzI [I₁.filter (· < x), I₁.filter fun y => x < y] ++ tail := by
  have h : stackOf n (σ ++ [x]) =
      some (nzI [I₁.filter (· < x), I₁.filter fun y => x < y] ++ tail) := by
    rw [stackOf_succ hleg, hst, step_active hx hge hmem]
  exact ⟨by rw [Legal, h]; rfl, by rw [stack, h]; rfl⟩

/-- **Legal moves at a nonempty stack**: a new minimum, or a value of the active head. -/
theorem legal_succ_iff_cons (hleg : Legal n σ) {I₁ : Finset ℕ} {tail : List (Finset ℕ)}
    (hst : stack n σ = I₁ :: tail) :
    Legal n (σ ++ [x]) ↔ (x ∈ unread n σ ∧ (x < m n σ ∨ x ∈ I₁)) := by
  constructor
  · intro h
    refine ⟨h.mem_unread, ?_⟩
    by_contra hcon
    rw [not_or] at hcon
    rw [Legal, stackOf_succ hleg, hst, step_deferred (by omega) hcon.2] at h
    exact Bool.noConfusion h
  · rintro ⟨hx, hlt | hmem⟩
    · exact (legal_succ_of_newMin_cons hleg hst hx hlt).1
    · by_cases hlt : x < m n σ
      · exact (legal_succ_of_newMin_cons hleg hst hx hlt).1
      · exact (legal_succ_of_active hleg hst hx hlt hmem).1

/-- **Legal moves at an empty stack**: only a new minimum. -/
theorem legal_succ_iff_nil (hleg : Legal n σ) (hst : stack n σ = []) :
    Legal n (σ ++ [x]) ↔ (x ∈ unread n σ ∧ x < m n σ) := by
  constructor
  · intro h
    refine ⟨h.mem_unread, ?_⟩
    by_contra hcon
    rw [Legal, stackOf_succ hleg, hst, step_empty_stack hcon] at h
    exact Bool.noConfusion h
  · rintro ⟨hx, hlt⟩
    exact (legal_succ_of_newMin_nil hleg hst hx hlt).1

/-- **The new-minimum transition** at a nonempty stack (the paper's merger): the control
becomes the number `h` of unread values below the new minimum, and the active head grows to
`ℓ₁ + p - 1 - h`. -/
theorem L_succ_newMin_cons (hleg : Legal n σ) {I₁ : Finset ℕ} {tail : List (Finset ℕ)}
    (hst : stack n σ = I₁ :: tail) (hx : x ∈ unread n σ) (hlt : x < m n σ)
    (hI₁ : ∀ y ∈ I₁, m n σ < y) :
    p n (σ ++ [x]) = below n σ x ∧
      L n (σ ++ [x]) = (I₁.card + p n σ - 1 - below n σ x) :: tail.map Finset.card := by
  refine ⟨p_succ_newMin hlt, ?_⟩
  rw [L, (legal_succ_of_newMin_cons hleg hst hx hlt).2, List.map_cons]
  have hdisj : Disjoint (mergeSet n σ x) I₁ := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [mergeSet, Finset.mem_filter] at ha
    exact absurd (hI₁ a hb) (by omega)
  rw [Finset.card_union_of_disjoint hdisj]
  have := card_mergeSet hx hlt
  congr 1
  omega

/-- **The new-minimum transition** at an empty stack. -/
theorem L_succ_newMin_nil (hleg : Legal n σ) (hst : stack n σ = []) (hx : x ∈ unread n σ)
    (hlt : x < m n σ) :
    p n (σ ++ [x]) = below n σ x ∧
      L n (σ ++ [x]) = nz [p n σ - 1 - below n σ x] := by
  refine ⟨p_succ_newMin hlt, ?_⟩
  rw [L, (legal_succ_of_newMin_nil hleg hst hx hlt).2, map_card_nzI]
  have := card_mergeSet hx hlt
  simp only [List.map_cons, List.map_nil]
  congr 2
  omega

/-- **The active-head transition**: reading the value of local rank `r + 1` of the head
replaces the head by the two parts of sizes `r` and `ℓ₁ - 1 - r`, with empty parts deleted.
The control does not change. -/
theorem L_succ_active (hleg : Legal n σ) {I₁ : Finset ℕ} {tail : List (Finset ℕ)}
    (hst : stack n σ = I₁ :: tail) (hx : x ∈ unread n σ) (hge : ¬ x < m n σ) (hmem : x ∈ I₁) :
    p n (σ ++ [x]) = p n σ ∧
      L n (σ ++ [x]) =
        nz [(I₁.filter (· < x)).card, I₁.card - 1 - (I₁.filter (· < x)).card]
          ++ tail.map Finset.card := by
  refine ⟨p_succ_active (by omega), ?_⟩
  rw [L, (legal_succ_of_active hleg hst hx hge hmem).2, List.map_append, map_card_nzI]
  have hsplit := card_filter_lt_add_card_filter_gt hmem
  have hB : (I₁.filter fun y => x < y).card = I₁.card - 1 - (I₁.filter (· < x)).card := by omega
  simp only [List.map_cons, List.map_nil, hB]

/-! ### The measure `ρ₁ = p + |L|`

The paper's \eqref{eq:rho-scalar}: the control mass plus the total interval size is the
number of unread values, and it drops by one at every move.  This is the measure on which
the induction proving `A_eq_W` runs. -/

theorem card_stackUnion (st : List (Finset ℕ))
    (h : st.Pairwise fun I J => ∀ a ∈ I, ∀ b ∈ J, a < b) :
    (stackUnion st).card = (st.map Finset.card).sum := by
  induction st with
  | nil => simp [stackUnion]
  | cons I t ih =>
    obtain ⟨hcross, hpt⟩ := List.pairwise_cons.mp h
    have hdisj : Disjoint I (stackUnion t) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      rw [mem_stackUnion] at hb
      obtain ⟨J, hJ, haJ⟩ := hb
      exact absurd (hcross J hJ a ha a haJ) (by omega)
    rw [stackUnion_cons, Finset.card_union_of_disjoint hdisj, ih hpt, List.map_cons,
      List.sum_cons]

theorem IsWord.length_le (hw : IsWord n σ) : σ.length ≤ n := by
  have h1 : σ.toFinset ⊆ Finset.range n := fun y hy =>
    Finset.mem_range.mpr (hw.2 y (List.mem_toFinset.mp hy))
  have h2 := Finset.card_le_card h1
  rwa [List.toFinset_card_of_nodup hw.1, Finset.card_range] at h2

theorem card_unread (hw : IsWord n σ) : (unread n σ).card = n - σ.length := by
  rw [unread, Finset.card_sdiff_of_subset (fun y hy =>
    Finset.mem_range.mpr (hw.2 y (List.mem_toFinset.mp hy)))]
  rw [Finset.card_range, List.toFinset_card_of_nodup hw.1]

/-- Every move drops the measure by one. -/
theorem card_unread_succ (hleg : Legal n (σ ++ [x])) :
    (unread n (σ ++ [x])).card + 1 = (unread n σ).card := by
  rw [unread_append_singleton, Finset.card_erase_of_mem hleg.mem_unread]
  have := Finset.card_pos.mpr ⟨x, hleg.mem_unread⟩
  omega

/-! ### The main theorems

The four statements below are the content of component 3a; they are proved in
`Av12453.OneThreshold.Invariant` (A), `Av12453.OneThreshold.Semantics` (B and C) and
`Av12453.OneThreshold.Counting` (D). -/

/-- **(A) The layout invariant.**  Every legal prefix has the ordered layout
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
    rw [mem_unread] at hy
    simp only [m_nil]
    omega
  | append_singleton τ x ih =>
    have hτ : Legal n τ := hleg.of_append_singleton
    have hlay : Layout n τ := ih hτ
    have hw : IsWord n τ := hτ.isWord
    have hx : x ∈ unread n τ := hleg.mem_unread
    have hun : unread n (τ ++ [x]) = (unread n τ).erase x := unread_append_singleton
    have hmnot : m n τ ∉ unread n τ := m_not_unread hw
    by_cases hlt : x < m n τ
    · have hm' : m n (τ ++ [x]) = x := m_succ_newMin hlt
      cases hst : stack n τ with
      | cons I₁ tail =>
        have hI₁mem : I₁ ∈ stack n τ := by rw [hst]; exact List.mem_cons_self
        have htailmem : ∀ J ∈ tail, J ∈ stack n τ := by
          intro J hJ; rw [hst]; exact List.mem_cons_of_mem _ hJ
        obtain ⟨-, hstack⟩ := legal_succ_of_newMin_cons hτ hst hx hlt
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
          · have h1 : m n τ < b := hlay.lt_of_mem (htailmem J hJ) hb
            rw [mem_mergeSet] at haE
            omega
          · exact hcross J hJ a haI b hb
        · rw [hun, hm']
          ext y
          constructor
          · intro hy
            rw [mem_stackUnion] at hy
            obtain ⟨I, hI, hyI⟩ := hy
            rcases List.mem_cons.mp hI with rfl | hI
            · rcases Finset.mem_union.mp hyI with h | h
              · rw [mem_mergeSet] at h
                exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨by omega, h.1⟩, h.2.1⟩
              · have h1 := hlay.unread_of_mem hI₁mem h
                have h2 := hlay.lt_of_mem hI₁mem h
                exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨by omega, h1⟩, by omega⟩
            · have h1 := hlay.unread_of_mem (htailmem I hI) hyI
              have h2 := hlay.lt_of_mem (htailmem I hI) hyI
              exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨by omega, h1⟩, by omega⟩
          · intro hy
            rw [Finset.mem_filter, Finset.mem_erase] at hy
            obtain ⟨⟨hyx, hyu⟩, hxy⟩ := hy
            rw [mem_stackUnion]
            rcases lt_trichotomy y (m n τ) with h | h | h
            · exact ⟨_, List.mem_cons_self,
                Finset.mem_union_left _ (mem_mergeSet.mpr ⟨hyu, hxy, h⟩)⟩
            · exact absurd (h ▸ hyu) hmnot
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
            rcases lt_trichotomy y (m n τ) with h | h | h
            · exact Finset.mem_union_left _ (mem_mergeSet.mpr ⟨hyu, by omega, h⟩)
            · exact absurd (h ▸ hyu) hmnot
            · have hbI₁ : b ∈ I₁ := by
                rcases Finset.mem_union.mp hb with hbE | hbI
                · rw [mem_mergeSet] at hbE; omega
                · exact hbI
              exact Finset.mem_union_right _ (hlay.head_initial hst hyu h hbI₁ hyb)
          · exact hlay.runs I (htailmem I hI) a ha b hb y hyu hay hyb
      | nil =>
        obtain ⟨-, hstack⟩ := legal_succ_of_newMin_nil hτ hst hx hlt
        have hempty : ∀ y, y ∈ unread n τ → ¬ (m n τ < y) := by
          intro y hy hmy
          obtain ⟨I, hI, -⟩ := hlay.exists_mem hy hmy
          rw [hst] at hI
          exact absurd hI (by simp)
        refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hstack]
        · intro I hI
          exact (mem_nzI.mp hI).2
        · exact List.Pairwise.sublist (nzI_sublist _) (by simp)
        · rw [hun, hm', stackUnion_nzI, stackUnion_cons, stackUnion]
          simp only [List.foldr_nil, Finset.union_empty]
          ext y
          rw [mem_mergeSet, Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨hyu, hxy, hym⟩
            exact ⟨⟨by omega, hyu⟩, hxy⟩
          · rintro ⟨⟨hyx, hyu⟩, hxy⟩
            refine ⟨hyu, hxy, ?_⟩
            rcases lt_trichotomy y (m n τ) with h | h | h
            · exact h
            · exact absurd (h ▸ hyu) hmnot
            · exact absurd h (hempty y hyu)
        · intro I hI a ha b hb y hy hay hyb
          rw [mem_nzI] at hI
          rw [List.mem_singleton] at hI
          rw [hI.1] at ha hb ⊢
          rw [mem_mergeSet] at ha hb ⊢
          rw [hun, Finset.mem_erase] at hy
          exact ⟨hy.2, by omega, by omega⟩
    · have hm' : m n (τ ++ [x]) = m n τ := m_succ_active (by omega)
      cases hst : stack n τ with
      | nil => exact absurd ((legal_succ_iff_nil hτ hst).mp hleg).2 hlt
      | cons I₁ tail =>
        have hI₁mem : I₁ ∈ stack n τ := by rw [hst]; exact List.mem_cons_self
        have htailmem : ∀ J ∈ tail, J ∈ stack n τ := by
          intro J hJ; rw [hst]; exact List.mem_cons_of_mem _ hJ
        have hmem : x ∈ I₁ := ((legal_succ_iff_cons hτ hst).mp hleg).2.resolve_left hlt
        obtain ⟨-, hstack⟩ := legal_succ_of_active hτ hst hx hlt hmem
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
        · rw [hun, hm', stackUnion_append, stackUnion_nzI]
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
            · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨by omega, h1⟩
            · rintro ⟨h1, h2⟩
              rcases lt_trichotomy y x with h | h | h
              · exact Or.inl ⟨h2, h⟩
              · exact absurd h h1
              · exact Or.inr ⟨h2, h⟩
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

/-- Every interval size is positive, so `W` is always evaluated at a genuine composition. -/
theorem L_pos (hleg : Legal n σ) : ∀ a ∈ L n σ, 0 < a := by
  intro a ha
  rw [L, List.mem_map] at ha
  obtain ⟨I, hI, rfl⟩ := ha
  exact Finset.card_pos.mpr ((layout_of_legal hleg).nonempty I hI)

/-- **The measure** \eqref{eq:rho-scalar}: `ρ₁(p, L) = p + |L|` is the number of unread
values. -/
theorem rho_eq (hleg : Legal n σ) : p n σ + (L n σ).sum = (unread n σ).card := by
  have hlay := layout_of_legal hleg
  have hw := hleg.isWord
  rw [L, ← card_stackUnion _ hlay.ordered, hlay.union, p, below]
  have hsplit : unread n σ =
      (unread n σ).filter (· < m n σ) ∪ (unread n σ).filter fun y => m n σ < y := by
    ext y
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hy
      rcases lt_trichotomy y (m n σ) with h | h | h
      · exact Or.inl ⟨hy, h⟩
      · exact absurd (h ▸ hy) (m_not_unread hw)
      · exact Or.inr ⟨hy, h⟩
    · rintro (⟨hy, -⟩ | ⟨hy, -⟩) <;> exact hy
  conv_rhs => rw [hsplit]
  rw [Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_filter] at ha hb
  omega

/-! ### The four main theorems

They are stated and proved in the three downstream modules, in this same namespace, with
exactly the statements that were frozen here as `sorry`-ed placeholders during Phase 2:

* **(A)** `sep_invariant`, in `Av12453/OneThreshold/Invariant.lean`;
* **(B)** `deferred_no_completion` and **(C)** `legal_complete_avoids`, in
  `Av12453/OneThreshold/Semantics.lean`;
* **(D-iii)** `A_eq_W` and the goal of component 3a, `av1342_count`, in
  `Av12453/OneThreshold/Counting.lean`.
-/

/-! ### Sanity checks

The running example of the paper, `π = 9,11,10,14,5,12,6,2,3,8,4,7,1,13,15`
(\eqref{eq:running-example}), written `0`-based, and its scan, tabulated in
\cref{ex:1342-scan}.  Every check below is a kernel evaluation (`decide`), so it adds no
axiom. -/

/-- The paper's running example \eqref{eq:running-example}, `0`-based. -/
def runningExample : List ℕ := [8, 10, 9, 13, 4, 11, 5, 1, 2, 7, 3, 6, 0, 12, 14]

set_option maxRecDepth 100000 in
/-- The scan of the running example is legal at every step. -/
example : Legal 15 runningExample := by decide

set_option maxRecDepth 100000 in
/-- Row `5` of \cref{ex:1342-scan}: after `9,11,10,14,5` the stack is
`{6,7,8,12,13} | {15}`, which `0`-based is `{5,6,7,11,12} | {14}`. -/
example : stack 15 (runningExample.take 5) = [{5, 6, 7, 11, 12}, {14}] := by decide

set_option maxRecDepth 100000 in
/-- The whole interval-stack column of \cref{ex:1342-scan}, `0`-based. -/
example : (List.range 16).map (fun k => stack 15 (runningExample.take k)) =
    [[], [{9, 10, 11, 12, 13, 14}], [{9}, {11, 12, 13, 14}], [{11, 12, 13, 14}],
      [{11, 12}, {14}], [{5, 6, 7, 11, 12}, {14}], [{5, 6, 7}, {12}, {14}],
      [{6, 7}, {12}, {14}], [{2, 3, 6, 7}, {12}, {14}], [{3, 6, 7}, {12}, {14}],
      [{3, 6}, {12}, {14}], [{6}, {12}, {14}], [{12}, {14}], [{12}, {14}], [{14}], []] := by
  decide

set_option maxRecDepth 100000 in
/-- The `W_p(L)` column of \cref{ex:1342-scan}: the interval sizes. -/
example : (List.range 16).map (fun k => L 15 (runningExample.take k)) =
    [[], [6], [1, 4], [4], [2, 1], [5, 1], [3, 1, 1], [2, 1, 1], [4, 1, 1], [3, 1, 1],
      [2, 1, 1], [1, 1, 1], [1, 1], [1, 1], [1], []] := by decide

set_option maxRecDepth 100000 in
/-- The `W_p(L)` column of \cref{ex:1342-scan}: the controls. -/
example : (List.range 16).map (fun k => p 15 (runningExample.take k)) =
    [15, 8, 8, 8, 8, 4, 4, 4, 1, 1, 1, 1, 1, 0, 0, 0] := by decide

set_option maxRecDepth 100000 in
/-- `|Av₄(1342)| = 23`. -/
example : W 4 [] = 23 := by decide

set_option maxRecDepth 100000 in
/-- `|Av₅(1342)| = 103`. -/
example : W 5 [] = 103 := by decide

set_option maxRecDepth 400000 in
/-- The first terms `1, 1, 2, 6, 23, 103` of `|Av_n(1342)|` (Bona's sequence; the paper's
\eqref{eq:first-terms} is the `d = 2` sequence of `Av(12453)`, not this one). -/
example : (List.range 6).map (fun k => W k []) = [1, 1, 2, 6, 23, 103] := by decide

end OneThreshold
end Av12453
