import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_IsAffineOpen_isRegularLocalRing_stalk_of_isRegularRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsAffineOpen_isRegularLocalRing_stalk_of_isRegularRing.lean)
-/
@[main]
private lemma main
  {X : Scheme.{u}}
  {U : X.Opens}
  {x : X}
-- given
  (hU : IsAffineOpen U)
  (hreg : IsRegularRing Γ(X, U))
  (hx : x ∈ U) :
-- imply
  IsRegularLocalRing (X.presheaf.stalk x) := by
-- proof
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨x, hx⟩
  have := hreg
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal) (X.presheaf.stalk x)).toRingEquiv


-- created on 2026-10-05
