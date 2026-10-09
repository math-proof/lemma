import Mathlib.MvPolynomial.PDeriv

/-!
# Commutativity of partial derivatives and mixed differentials

This file establishes that partial derivatives of multivariate polynomials
commute, and introduces the *mixed differential* operator `(1 - ∂ᵢ)` applied
in list order. Several algebraic identities of the mixed differential are
proved: it depends only on the multiset of indices, distributes over
append as function composition, and commutes with each `∂ᵢ`.
-/

namespace MvPolynomial

/-- Partial derivatives of a multivariate polynomial commute. -/
theorem pderiv_comm {σ R : Type*} [CommSemiring R]
    (i j : σ) (p : MvPolynomial σ R) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  by_cases h : i = j
  · subst j
    rfl
  · ext s
    simp only [coeff_pderiv]
    rw [show s + Finsupp.single i 1 + Finsupp.single j 1 =
      s + Finsupp.single j 1 + Finsupp.single i 1 by abel]
    simp [h, Ne.symm h]
    ring

/-- Apply the operators `1 - ∂ᵢ`, in list order, to a multivariate polynomial. -/
noncomputable def mixedDifferential {σ R : Type*} [CommRing R]
    (indices : List σ) (p : MvPolynomial σ R) : MvPolynomial σ R :=
  indices.foldl (fun q i ↦ q - pderiv i q) p

/-- Applying no mixed differential operators leaves a polynomial unchanged. -/
@[simp]
theorem mixedDifferential_nil {σ R : Type*} [CommRing R]
    (p : MvPolynomial σ R) : mixedDifferential [] p = p := by
  rfl

/-- The first mixed differential operator can be peeled from the defining list. -/
theorem mixedDifferential_cons {σ R : Type*} [CommRing R]
    (i : σ) (iis : List σ) (p : MvPolynomial σ R) :
    mixedDifferential (i :: iis) p = mixedDifferential iis (p - pderiv i p) := by
  rfl

/-- The mixed differential operator depends only on the multiset of differentiation indices. -/
theorem mixedDifferential_eq_of_perm {σ R : Type*} [CommRing R]
    {iis js : List σ} (h : iis.Perm js) (p : MvPolynomial σ R) :
    mixedDifferential iis p = mixedDifferential js p := by
  induction h generalizing p with
  | nil => rfl
  | cons i h ih =>
      rw [mixedDifferential_cons, mixedDifferential_cons]
      exact ih _
  | swap i j iis =>
      rw [mixedDifferential_cons, mixedDifferential_cons, mixedDifferential_cons,
        mixedDifferential_cons]
      congr 1
      rw [map_sub, map_sub, pderiv_comm]
      abel
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ p).trans (ih₂ p)

/-- Applying mixed differential operators to an appended list is function composition. -/
theorem mixedDifferential_append {σ R : Type*} [CommRing R]
    (iis js : List σ) (p : MvPolynomial σ R) :
    mixedDifferential (iis ++ js) p = mixedDifferential js (mixedDifferential iis p) := by
  simp only [mixedDifferential, List.foldl_append]

/-- Partial differentiation commutes with every mixed differential operator. -/
theorem pderiv_mixedDifferential {σ R : Type*} [CommRing R]
    (i : σ) (iis : List σ) (p : MvPolynomial σ R) :
    pderiv i (mixedDifferential iis p) = mixedDifferential iis (pderiv i p) := by
  induction iis generalizing p with
  | nil => rfl
  | cons j js ih =>
      rw [mixedDifferential_cons, mixedDifferential_cons, ih]
      congr 1
      rw [map_sub, pderiv_comm]

end MvPolynomial
