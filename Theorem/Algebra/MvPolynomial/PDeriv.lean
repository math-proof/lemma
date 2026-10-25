import Mathlib.Algebra.MvPolynomial.PDeriv
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

end MvPolynomial
