import Def.AlgebraicGeometry_PolarisedAbelianScheme
import Structure.AlgebraicGeometry_FramedPolarisedAbelianScheme

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

namespace Scheme.Modules


end Scheme.Modules


namespace FramedPolarisedAbelianScheme

variable {g N n : ℕ}

def Iso {S : Type u} [CommRing S] (X X' : FramedPolarisedAbelianScheme g N n S) : Prop :=
  ∃ (e : X.A ≅ X'.A) (he : e.hom ≫ X'.f = X.f),
    e.hom ≫ X'.frame.toProj = X.frame.toProj ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t X.f),
      (X.L.mul t x y).1 ≫ e.hom =
        (X'.L.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1) ∧
    (∀ i, (X.P i).1 ≫ e.hom = (X'.P i).1) ∧
    (∀ s : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (X.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback e.hom).obj X'.pol) ≅
        (Scheme.Modules.pullback (X.f ⁻¹ᵁ U).ι).obj X.pol))


end FramedPolarisedAbelianScheme

end AlgebraicGeometry

end
