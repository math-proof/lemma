import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_isIntegral_of_smoothOfRelativeDimension_one_of_geometricallyIntegral](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isIntegral_of_smoothOfRelativeDimension_one_of_geometricallyIntegral.lean)
-/
@[path]
private lemma main
  {k : Type} [Field k] {C : (Scheme : Type 1)} (c : C ⟶ Spec (CommRingCat.of k))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] :
  -- imply
  IsIntegral C :=
  GeometricallyIntegral.isIntegral_of_subsingleton c


-- created on 2026-10-20
