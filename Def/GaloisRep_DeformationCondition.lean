import Mathlib
import Def.GaloisRep_Adic

set_option autoImplicit false

noncomputable section

namespace GaloisRep

open IsLocalRing

variable (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]

def TangentFinite (ρbar : ResidualGaloisRep (ResidueField 𝒪))
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop) : Prop :=
  letI : Algebra 𝒪 (DualNumber (ResidueField 𝒪)) :=
    ((algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪))).comp
      (algebraMap 𝒪 (ResidueField 𝒪))).toAlgebra
  letI : Algebra (ResidueField 𝒪) (ResidueField (DualNumber (ResidueField 𝒪))) :=
    ((IsLocalRing.residue (DualNumber (ResidueField 𝒪))).comp
      (algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪)))).toAlgebra
  Finite (Quotient (⟨fun ρ ρ' : {ρ : GaloisRepAdic (DualNumber (ResidueField 𝒪)) //
      𝒟 ρ ∧ ρ.residual.IsEquiv (ρbar.baseChange (ResidueField (DualNumber (ResidueField 𝒪)))) } =>
      ρ.1.IsEquiv ρ'.1, ⟨fun ρ => ⟨GaloisRepAdic.Equiv.refl ρ.1⟩,
        fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩⟩ : Setoid _))

end GaloisRep

end
