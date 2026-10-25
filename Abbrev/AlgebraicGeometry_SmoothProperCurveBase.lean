import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Fiber
import Structure.AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits NeronModelInfra

universe u

namespace AlgebraicGeometry


namespace SmoothProperCurve

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))

section BaseChange

variable (T : Type u) [CommRing T] [Algebra R T]

abbrev specMap : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R T))

abbrev baseChange : pullback c (specMap R T) ⟶ Spec (CommRingCat.of T) :=
  pullback.snd c (specMap R T)

variable {R c}

end BaseChange


end SmoothProperCurve

end AlgebraicGeometry

end
