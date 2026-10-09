import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_IsAffineOpen_ringKrullDim_stalk_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsAffineOpen_ringKrullDim_stalk_le.lean)
-/
@[path]
private lemma main
  {X : Scheme.{u}}
  {U : X.Opens}
  {x : X}
-- given
  (hU : IsAffineOpen U)
  (hx : x ∈ U) :
-- imply
  ringKrullDim (X.presheaf.stalk x) ≤ ringKrullDim Γ(X, U) := by
-- proof
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨x, hx⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨x, hx⟩).asIdeal (X.presheaf.stalk x)]
  exact Ideal.height_le_ringKrullDim_of_isPrime


-- created on 2026-10-03
