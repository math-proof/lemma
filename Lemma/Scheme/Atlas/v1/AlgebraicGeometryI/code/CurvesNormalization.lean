import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.CurvesNormalization
open Algebra


/--
[finite_birational_normal_algebraMap_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurvesNormalization.lean)
-/
@[path]
lemma finite_birational_normal_algebraMap_bijective
  {B A K : Type*}
  [CommRing B]
  [IsDomain B]
  [CommRing A]
  [Field K]
  [Algebra B K]
  [IsFractionRing B K]
  [Algebra A K]
  [Algebra B A]
  [IsScalarTower B A K]
  [IsIntegrallyClosed B]
  [IsIntegralClosure A B K] :
-- imply
  Function.Bijective (algebraMap B A) := by
-- proof
  have : IsIntegralClosure B B K := (isIntegrallyClosed_iff_isIntegralClosure K).mp inferInstance
  let e := IsIntegralClosure.equiv B A K B
  have key : (e.symm : B → A) = algebraMap B A := by
    ext b
    have h1 : e.symm b = e.symm (algebraMap B B b) := by simp
    exact h1.trans (e.symm.commutes b)
  rwa [← key]
section Normalization
set_option backward.isDefEq.respectTransparency false in

/--
[normalization_is_normal_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurvesNormalization.lean)
-/
@[path]
lemma normalization_is_normal_general
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra A L]
  [IsScalarTower A K L] :
-- imply
  IsIntegrallyClosed (integralClosure A L) :=
-- proof
  integralClosure.isIntegrallyClosedOfFiniteExtension K

/--
[normalization_map_injective_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurvesNormalization.lean)
-/
@[path]
lemma normalization_map_injective_general
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [Algebra A L]
  [IsScalarTower A K L] :
-- imply
  Function.Injective (algebraMap A (integralClosure A L)) := by
-- proof
  haveI : IsScalarTower A (integralClosure A L) L :=
    IsScalarTower.subalgebra' A L L (integralClosure A L)
  exact algebraMap_injective_of_field_isFractionRing A (↥(integralClosure A L)) K L


-- created on 2026-10-23
