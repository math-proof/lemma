-- Carved from Lemma/Definitions/Def_PadicComplex_GaloisAction.lean: instance decls only.
import Mathlib

set_option autoImplicit false

noncomputable section

open UniformSpace

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]


instance uniformContinuousConstSMul_gal :
    UniformContinuousConstSMul (Gal p) (PadicAlgCl p) :=
  ⟨fun σ => (isometry_algEquiv p σ).uniformContinuous⟩


instance mulSemiringAction : MulSemiringAction (Gal p) ℂ_[p] :=
  { (inferInstance : DistribMulAction (Gal p) ℂ_[p]) with
    smul_one := fun σ => by
      rw [← Completion.coe_one, smul_coe, map_one]
    smul_mul := fun σ x y => by
      refine Completion.induction_on₂ x y ?_ ?_
      · exact isClosed_eq ((continuous_fst.mul continuous_snd).const_smul σ)
          ((continuous_fst.const_smul σ).mul (continuous_snd.const_smul σ))
      · intro a b
        rw [← Completion.coe_mul, smul_coe, smul_coe, smul_coe, map_mul, Completion.coe_mul] }


instance smulCommClass_gal_padic : SMulCommClass (Gal p) ℚ_[p] ℂ_[p] :=
  inferInstance

instance smulCommClass_padic_gal : SMulCommClass ℚ_[p] (Gal p) ℂ_[p] :=
  SMulCommClass.symm _ _ _


end PadicComplex

end
