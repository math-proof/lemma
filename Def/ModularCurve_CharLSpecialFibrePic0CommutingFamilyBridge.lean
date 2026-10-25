import Lemma.Scheme.CharLSpecialFibrePic0ForallMBridge
import Instance.ModularCurve_SpecializationWitness

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1200000

noncomputable section
open AlgebraicCurve

namespace ModularCurve

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable [IsAlgClosed K] [IsCurveOver K (modularFunctionFieldC K N)]
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

def Pic0SpecialFibreCommutingFamilyMatch
    (fam : CommutingHeckeFamily (Pic0 K (modularFunctionFieldC K N))) : Prop :=
  fam.T ⟨ℓ, hℓ.out⟩
    = (heckeFibreGeomLevelPic0OfIsCurveOver K N data hKr).toIntLinearMap

end ModularCurve

end
