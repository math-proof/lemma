import Def.AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Lemma.AlgebraicGeometry.ModulesPullbackLocalSection
import Structure.AlgebraicGeometry_ThetaGroupAction

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.Polarisation

variable {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)


theorem translate_snd {R : Type u} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver t f) : translate f L t x ≫ pullback.snd f t = pullback.snd f t :=
  pullback.lift_snd _ _ _


namespace ThetaPt

variable {f} {L} {𝓛 : A.Modules} {R : Type u} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)}


end ThetaPt


end AlgebraicGeometry.Polarisation

end
