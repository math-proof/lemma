import Mathlib
import Abbrev.FreyPackage_ModMCarrier_LatticeRed
import Abbrev.FreyPackage_ModMCarrier_Rescale
import Def.CuspForm_IntegralStructure
import Structure.ModularForm_AtkinLehnerDatum
import Instance.FreyPackage_ModMCarrier_OldSublattice

set_option autoImplicit false
noncomputable section
open CongruenceSubgroup ModularForm
open scoped TensorProduct

namespace FreyPackage.ModMCarrier

end FreyPackage.ModMCarrier

namespace FreyPackage.ModMCarrier

section WitnessResidueField

abbrev WitnessResidueField (𝔪 : Ideal (integralClosure ℤ ℂ)) : Type :=
  (integralClosure ℤ ℂ) ⧸ 𝔪

abbrev witnessResidueMap (𝔪 : Ideal (integralClosure ℤ ℂ)) :
    integralClosure ℤ ℂ →+* WitnessResidueField 𝔪 :=
  Ideal.Quotient.mk 𝔪

end WitnessResidueField

section OldSublattice
variable {M q' : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q')

section ReducedMaps
variable (k : Type*) [Field k]

end ReducedMaps
end OldSublattice

section OfPrimeNotDvd
variable (N q' : ℕ)

end OfPrimeNotDvd

end FreyPackage.ModMCarrier
