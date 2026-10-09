import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_IsOpenImmersion_isRegularLocalRing_stalk_iff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsOpenImmersion_isRegularLocalRing_stalk_iff.lean)
-/
@[path]
private lemma main
  {U X : Scheme.{u}}
  {i : U ⟶ X} [IsOpenImmersion i]
  {u : U} :
-- imply
  IsRegularLocalRing (X.presheaf.stalk (i.base u)) ↔ IsRegularLocalRing (U.presheaf.stalk u) := by
-- proof
  let e : X.presheaf.stalk (i.base u) ≃+* U.presheaf.stalk u := (asIso (i.stalkMap u)).commRingCatIsoToRingEquiv
  exact ⟨fun h => IsRegularLocalRing.of_ringEquiv e, fun h => IsRegularLocalRing.of_ringEquiv e.symm⟩


-- created on 2026-10-03
