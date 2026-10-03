import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_jacobsonSpace_of_locallyOfFiniteType](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_jacobsonSpace_of_locallyOfFiniteType.lean)
-/
@[main]
private lemma main
  {k : Type u} [Field k]
  {X : Scheme.{u}}
  {t : X ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType t] :
-- imply
  JacobsonSpace X :=
-- proof
  LocallyOfFiniteType.jacobsonSpace t


-- created on 2026-10-03
