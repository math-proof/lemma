import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_IsOpenImmersion_ringKrullDim_stalk_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsOpenImmersion_ringKrullDim_stalk_eq.lean)
-/
@[path]
private lemma main
  {U X : Scheme.{u}}
  {i : U ⟶ X} [IsOpenImmersion i]
  {u : U} :
-- imply
  ringKrullDim (U.presheaf.stalk u) = ringKrullDim (X.presheaf.stalk (i.base u)) :=
-- proof
  (ringKrullDim_eq_of_ringEquiv (asIso (i.stalkMap u)).commRingCatIsoToRingEquiv).symm


-- created on 2026-10-03
