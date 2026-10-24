import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.DerivedFunctorsDefs
open CategoryTheory CategoryTheory.Limits DerivedFunctorsDefs


namespace DerivedFunctorsDefs

/--
[rightDerived_injective_vanishing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DerivedFunctorsDefs.lean)
-/
@[path]
lemma rightDerived_injective_vanishing
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {C D}
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  [EnoughInjectives C]
  {F : C ⥤ D}
  [F.Additive]
  {n : ℕ}
  {X : C}
  [Injective X] :
-- imply
  IsZero ((rightDerivedFunctor F (n + 1)).obj X) :=
-- proof
  F.isZero_rightDerived_obj_injective_succ n X

end DerivedFunctorsDefs


-- created on 2026-10-23
