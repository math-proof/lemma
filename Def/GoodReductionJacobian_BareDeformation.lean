import Structure.JacJ1Iface
import Lemma.AlgebraicGeometry.RelativeGroupLaw
import Def.AlgebraicGeometry_FormalGroupAlongSection
import Structure.GoodReductionJacobian_BareDeformation

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian


namespace BareDeformation

variable {S : Type} [CommRing S] {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
  {B : Type} [CommRing B] [Algebra B S]

def IsIso (D D' : BareDeformation fₛ Lₛ B) : Prop :=
  ∃ e : D.A ≅ D'.A, e.hom ≫ D'.f = D.f ∧ D.g ≫ e.hom = D'.g

def LiftsCoordinates {d : ℕ} (D : BareDeformation fₛ Lₛ B)
    (θₛ : RelativeGroupLaw.FormalCoordinates fₛ d) (θ : RelativeGroupLaw.FormalCoordinates D.f d) : Prop :=
  ∀ (B'' : Type) [CommRing B''] [Algebra B B''] [Algebra S B''] [IsScalarTower B S B''] (s : Fin d → B''),
    (∀ i, IsNilpotent (s i)) → (θₛ B'' s).1 ≫ D.g = (θ B'' s).1

end BareDeformation

end GoodReductionJacobian

end
