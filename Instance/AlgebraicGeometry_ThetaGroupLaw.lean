-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_ThetaGroupLaw.lean: instance decls only.
import Lemma.AlgebraicGeometry.ThetaGroupAction
import Instance.AlgebraicGeometry_ThetaGroup
import Lemma.AlgebraicGeometry.ThetaGroupLaw

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian


namespace AlgebraicGeometry.Polarisation

instance PtGrp.instGroup {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : Group (PtGrp L t) := L.pointGroup t

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
variable {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))

namespace ThetaPt

variable {f} {L} {𝓛 : A.Modules} {t}

instance : Mul (ThetaPt f L 𝓛 t) := ⟨mul⟩
instance : One (ThetaPt f L 𝓛 t) := ⟨one⟩
instance : Inv (ThetaPt f L 𝓛 t) := ⟨inv⟩
instance : Div (ThetaPt f L 𝓛 t) := ⟨fun θ θ' => θ * θ'⁻¹⟩
instance : Pow (ThetaPt f L 𝓛 t) ℕ := ⟨fun θ n => npowRec n θ⟩
instance : Pow (ThetaPt f L 𝓛 t) ℤ := ⟨fun θ n => zpowRec npowRec n θ⟩

instance instGroup : Group (ThetaPt f L 𝓛 t) :=
  Function.Injective.group toGrp toGrp_injective toGrp_one toGrp_mul toGrp_inv toGrp_div toGrp_npow toGrp_zpow

end ThetaPt

end AlgebraicGeometry.Polarisation

end
