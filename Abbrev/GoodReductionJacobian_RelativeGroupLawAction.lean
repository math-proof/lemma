import Mathlib
import Structure.AlgebraicGeometry_RelativeGroupLaw

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}

abbrev actionSource (f : J ⟶ Spec (CommRingCat.of R)) {E : Scheme.{u}} (ι : E ⟶ J) :
    pullback (ι ≫ f) f ⟶ Spec (CommRingCat.of R) :=
  pullback.snd (ι ≫ f) f ≫ f

end GoodReductionJacobian.RelativeGroupLaw

end
