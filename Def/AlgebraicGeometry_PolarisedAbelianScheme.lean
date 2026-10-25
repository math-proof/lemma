import Mathlib.Topology.KrullDimension
import Structure.JacJ1Iface
import Lemma.GoodReductionJacobian.RelativeGroupLawKernel
import Def.AlgebraicGeometry_RelativePicardFunctor
import Def.AlgebraicGeometry_ModulesProjPresentation
import Structure.AlgebraicGeometry_PolarisedAbelianScheme

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace GoodReductionJacobian.RelativeGroupLaw


end GoodReductionJacobian.RelativeGroupLaw

namespace AlgebraicGeometry


namespace PolarisedAbelianScheme

variable {g d n : ℕ}

def Iso {S : Type u} [CommRing S] (u u' : PolarisedAbelianScheme g d n S) : Prop :=
  ∃ (e : u.A ≅ u'.A) (he : e.hom ≫ u'.f = u.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t u.f),
      (u.L.mul t x y).1 ≫ e.hom =
        (u'.L.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1) ∧
    (∀ i, (u.P i).1 ≫ e.hom = (u'.P i).1) ∧
    (∀ s : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback e.hom).obj u'.pol) ≅
        (Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj u.pol))


end PolarisedAbelianScheme

end AlgebraicGeometry

end
