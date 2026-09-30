/-
Copyright (c) 2026 Henning Ulfarsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Ulfarsson
-/
import Mathlib.Data.List.Sublists
import PermPatterns.Containment

/-!
# Decidability of `IsPermOf`, order isomorphism, containment and avoidance

Being a permutation of `{0, …, n-1}` is a condition on finitely many letters, order
isomorphism is an equivalence between two words checked at finitely many pairs of positions,
and containment quantifies over the finitely many sublists of a word.  The instances below
make `PermPatterns.IsPermOf` and the predicates of `PermPatterns.Containment` computable, so
that `decide` can evaluate them on concrete words and `Finset.filter` can use them.

## Main results

* `PermPatterns.orderIsomorphic_iff_getD` : order isomorphism in the bounded-quantifier form that
  the `Decidable` instance is built from.
* `PermPatterns.contains_iff_sublists` : containment as a search over `List.sublists`.
* `PermPatterns.decidableIsPermOf`, `PermPatterns.decidableOrderIsomorphic`,
  `PermPatterns.decidableContains`, `PermPatterns.decidableAvoids`,
  `PermPatterns.decidableAvoidsAll` : the instances themselves.
-/

namespace PermPatterns

/-- Being a permutation of `{0, …, n-1}` is decidable, by `PermPatterns.isPermOf_iff`. -/
instance decidableIsPermOf (n : ℕ) (w : List ℕ) : Decidable (IsPermOf n w) :=
  decidable_of_iff _ isPermOf_iff.symm

theorem orderIsomorphic_iff_getD (u v : List ℕ) :
    OrderIsomorphic u v ↔ u.length = v.length ∧
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

instance decidableOrderIsomorphic (u v : List ℕ) : Decidable (OrderIsomorphic u v) :=
  decidable_of_iff _ (orderIsomorphic_iff_getD u v).symm

theorem contains_iff_sublists (w τ : List ℕ) :
    Contains w τ ↔ ∃ s ∈ w.sublists, OrderIsomorphic s τ := by
  simp only [Contains, List.mem_sublists]

instance decidableContains (w τ : List ℕ) : Decidable (Contains w τ) :=
  decidable_of_iff _ (contains_iff_sublists w τ).symm

instance decidableAvoids (w τ : List ℕ) : Decidable (Avoids w τ) :=
  decidable_of_iff _ (avoids_iff (w := w) (τ := τ)).symm

instance decidableAvoidsAll (w : List ℕ) (B : Finset (List ℕ)) : Decidable (AvoidsAll w B) :=
  inferInstanceAs (Decidable (∀ τ ∈ B, Avoids w τ))

end PermPatterns
