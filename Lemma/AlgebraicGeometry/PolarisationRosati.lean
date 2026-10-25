import Def.AlgebraicGeometry_PolarisedAbelianScheme
import Abbrev.SheafOfModules_MonoidalV2
import Def.AlgebraicGeometry_PolarisationRosati

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.Polarisation

variable {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)


theorem negMor_over : negMor f L ≫ f = f := (L.inv f (idPt f)).2


theorem addMor_over : addMor f L ≫ f = pullback.fst f f ≫ f :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).2

end AlgebraicGeometry.Polarisation

end
