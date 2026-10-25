import Mathlib.Algebra.MvPolynomial.PDeriv
import Theorem.Algebra.MvPolynomial.PDeriv
/-!
# Commutativity of partial derivatives and mixed differentials

This file establishes that partial derivatives of multivariate polynomials
commute, and introduces the *mixed differential* operator `(1 - ∂ᵢ)` applied
in list order. Several algebraic identities of the mixed differential are
proved: it depends only on the multiset of indices, distributes over
append as function composition, and commutes with each `∂ᵢ`.
-/


namespace MvPolynomial

/-- Apply the operators `1 - ∂ᵢ`, in list order, to a multivariate polynomial. -/
noncomputable def mixedDifferential {σ R : Type*} [CommRing R]
    (indices : List σ) (p : MvPolynomial σ R) : MvPolynomial σ R :=
  indices.foldl (fun q i ↦ q - pderiv i q) p

end MvPolynomial
