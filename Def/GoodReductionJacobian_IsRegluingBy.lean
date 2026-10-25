import Def.GoodReductionJacobian_BareDeformation
import Instance.AlgebraicGeometry_OrderedAffineCoverCech

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.BareDeformation

variable {S : Type} [CommRing S] {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
  {B : Type} [CommRing B] [Algebra B S]

def IsRegluingBy (D₀ : BareDeformation fₛ Lₛ B) (𝒰 : D₀.A.OrderedAffineCover)
    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation fₛ Lₛ B) : Prop :=

  (∀ s : 𝒰.Idx 1, (τ s).hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f) ∧

  (∀ s : 𝒰.Idx 1, (D₀.g ∣_ 𝒰.inter s) ≫ (τ s).hom = D₀.g ∣_ 𝒰.inter s) ∧

  ∃ ι : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A,
    (∀ i, IsOpenImmersion (ι i)) ∧
    (∀ i, ι i ≫ D.f = (𝒰.U i).ι ≫ D₀.f) ∧
    (∀ x : D.A, ∃ (i : 𝒰.ι) (y : ↑(𝒰.U i)), (ι i).base y = x) ∧
    (∀ i, (D₀.g ∣_ 𝒰.U i) ≫ ι i = (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ D.g) ∧
    (∀ s : 𝒰.Idx 1,
      D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ι (s.1 0) = (τ s).hom ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι (s.1 1))

end GoodReductionJacobian.BareDeformation

end
