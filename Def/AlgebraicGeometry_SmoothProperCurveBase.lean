module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Fiber
public import Theorem.Scheme.NeronModelPropertyBundleCarrier
public import Abbrev.AlgebraicGeometry_SmoothProperCurveBase

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits NeronModelInfra

universe u

namespace AlgebraicGeometry


namespace SmoothProperCurve

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))

section BaseChange

variable (T : Type u) [CommRing T] [Algebra R T]

def sectionBaseChange (ε : SchemeHomOver (𝟙 _) c) : SchemeHomOver (𝟙 _) (baseChange R c T) :=
  ⟨pullback.lift (specMap R T ≫ ε.1) (𝟙 _) (by rw [Category.assoc, ε.2]; simp),
    pullback.lift_snd _ _ _⟩

end BaseChange


end SmoothProperCurve

end AlgebraicGeometry

end

end
