import Class.MvFormalGroup_BasicV2
import Structure.AlgebraicGeometry_RelativeGroupLaw
import Abbrev.CerednikDrinfeld_SchemeNilpPoints

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace MvFormalGroup

variable {B : Type} [CommRing B]

end MvFormalGroup

namespace GoodReductionJacobian.RelativeGroupLaw

variable {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}

abbrev FormalCoordinates (f : A ⟶ Spec (CommRingCat.of B)) (g : ℕ) : Type 1 :=
  ∀ (B' : Type) [CommRing B'] [Algebra B B'], (Fin g → B') → SchemeHomOver (Scheme.specOver (𝒪 := B) B') f

end GoodReductionJacobian.RelativeGroupLaw
