module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Fiber
public import Theorem.Scheme.NeronModelPropertyBundleCarrier
public import Abbrev.AlgebraicGeometry_SmoothProperCurveBase

public noncomputable section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits NeronModelInfra

universe u

namespace AlgebraicGeometry


namespace SmoothProperCurve

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))

section BaseChange

variable (T : Type u) [CommRing T] [Algebra R T]


@[simp]
public theorem sectionBaseChange_coe_fst (ε : SchemeHomOver (𝟙 _) c) :
    (sectionBaseChange T ε).1 ≫ pullback.fst c (specMap R T) = specMap R T ≫ ε.1 :=
  pullback.lift_fst _ _ _


@[simp]
public theorem sectionBaseChange_coe_snd (ε : SchemeHomOver (𝟙 _) c) :
    (sectionBaseChange T ε).1 ≫ pullback.snd c (specMap R T) = 𝟙 _ :=
  pullback.lift_snd _ _ _

end BaseChange


end SmoothProperCurve

end AlgebraicGeometry

end
