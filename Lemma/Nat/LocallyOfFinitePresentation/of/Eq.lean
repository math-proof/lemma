import Mathlib
import sympy.Basic

open AlgebraicGeometry CategoryTheory

/--
[AlgebraicGeometry_locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian.lean)
-/
@[main]
private lemma main
  {X Y S : Scheme.{u}} [IsLocallyNoetherian S]
  {f : X ⟶ S} [LocallyOfFiniteType f]
  {g : Y ⟶ S} [LocallyOfFiniteType g]
-- given
  (h : X ⟶ Y)
  (w : h ≫ g = f) :
-- imply
  LocallyOfFinitePresentation h := by
-- proof
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have : LocallyOfFiniteType (h ≫ g) := by rw [w]; infer_instance
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h g
  infer_instance


-- created on 2026-10-05
