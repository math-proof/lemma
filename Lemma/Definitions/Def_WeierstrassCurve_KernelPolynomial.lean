import Mathlib

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

noncomputable def kernelPolynomial (S : Finset (R × R)) : R[X] :=
  ∏ P ∈ S, (X - C P.1)

@[simp] theorem kernelPolynomial_empty : kernelPolynomial (∅ : Finset (R × R)) = 1 := by
  simp [kernelPolynomial]

theorem kernelPolynomial_cons {P : R × R} {S : Finset (R × R)} (hP : P ∉ S) :
    kernelPolynomial (Finset.cons P S hP) = (X - C P.1) * kernelPolynomial S := by
  simp [kernelPolynomial, Finset.prod_cons]

theorem kernelPolynomial_insert [DecidableEq R] {P : R × R} {S : Finset (R × R)} (hP : P ∉ S) :
    kernelPolynomial (insert P S) = (X - C P.1) * kernelPolynomial S := by
  simp [kernelPolynomial, Finset.prod_insert hP]

@[simp] theorem kernelPolynomial_singleton (P : R × R) :
    kernelPolynomial ({P} : Finset (R × R)) = X - C P.1 := by
  simp [kernelPolynomial]

theorem kernelPolynomial_eq_multiset_prod (S : Finset (R × R)) :
    kernelPolynomial S = ((S.val.map Prod.fst).map fun x => X - C x).prod := by
  rw [kernelPolynomial, Finset.prod_eq_multiset_prod, Multiset.map_map]
  rfl

theorem monic_kernelPolynomial (S : Finset (R × R)) : (kernelPolynomial S).Monic :=
  monic_prod_of_monic _ _ fun P _ => monic_X_sub_C P.1

theorem natDegree_kernelPolynomial [Nontrivial R] (S : Finset (R × R)) :
    (kernelPolynomial S).natDegree = S.card := by
  rw [kernelPolynomial, natDegree_prod_of_monic _ _ fun P _ => monic_X_sub_C P.1]
  simp

theorem eval_kernelPolynomial (S : Finset (R × R)) (x : R) :
    (kernelPolynomial S).eval x = ∏ P ∈ S, (x - P.1) := by
  simp [kernelPolynomial, eval_prod]

theorem eval_kernelPolynomial_eq_zero {S : Finset (R × R)} {P : R × R} (hP : P ∈ S) :
    (kernelPolynomial S).eval P.1 = 0 := by
  rw [eval_kernelPolynomial]
  exact Finset.prod_eq_zero hP (sub_self _)

theorem map_kernelPolynomial {S' : Type*} [CommRing S'] (f : R →+* S') (S : Finset (R × R)) :
    (kernelPolynomial S).map f = ∏ P ∈ S, (X - C (f P.1)) := by
  simp [kernelPolynomial, Polynomial.map_prod]

theorem map_kernelPolynomial_of_injOn {S' : Type*} [CommRing S'] [DecidableEq S'] (f : R →+* S')
    (S : Finset (R × R)) (hf : Set.InjOn (Prod.map f f) S) :
    (kernelPolynomial S).map f = kernelPolynomial (S.image (Prod.map f f)) := by
  rw [map_kernelPolynomial, kernelPolynomial, Finset.prod_image hf]
  simp

theorem roots_kernelPolynomial [IsDomain R] (S : Finset (R × R)) :
    (kernelPolynomial S).roots = S.val.map Prod.fst := by
  rw [kernelPolynomial_eq_multiset_prod, roots_multiset_prod_X_sub_C]

theorem eval_kernelPolynomial_eq_zero_iff [IsDomain R] {S : Finset (R × R)} {x : R} :
    (kernelPolynomial S).eval x = 0 ↔ ∃ P ∈ S, P.1 = x := by
  rw [eval_kernelPolynomial, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero, eq_comm]

end WeierstrassCurve
