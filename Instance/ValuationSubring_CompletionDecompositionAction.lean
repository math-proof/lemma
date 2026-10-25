-- Carved from Lemma/Definitions/Def_ValuationSubring_CompletionDecompositionAction.lean: instance decls only.
import Mathlib

set_option autoImplicit false

noncomputable section

open MonoidWithZeroHom WithZeroTopology UniformSpace

namespace ValuationSubring

variable {K : Type*} [Field K] (A : ValuationSubring K) (F : Type*) [Field F] [Algebra F K]


instance charZero_completion [CharZero K] : CharZero A.valuation.Completion :=
  charZero_of_injective_ringHom
    (UniformSpace.Completion.coeRingHom (α := WithVal A.valuation)).injective


instance mulSemiringActionWithVal :
    MulSemiringAction (A.decompositionSubgroup F) (WithVal A.valuation) where
  one_smul x := by rw [smul_withVal_def]; rfl
  mul_smul σ τ x := by simp only [smul_withVal_def]; rfl
  smul_zero σ := by rw [smul_withVal_def, WithVal.ofVal_zero, map_zero]; rfl
  smul_add σ x y := by simp only [smul_withVal_def, WithVal.ofVal_add, map_add]; rfl
  smul_one σ := by rw [smul_withVal_def, WithVal.ofVal_one, map_one]; rfl
  smul_mul σ x y := by simp only [smul_withVal_def, WithVal.ofVal_mul, map_mul]; rfl


instance uniformContinuousConstSMul_withVal [h : Fact (A.DecompositionIsometric F)] :
    UniformContinuousConstSMul (A.decompositionSubgroup F) (WithVal A.valuation) :=
  ⟨fun σ => uniformContinuous_addMonoidHom_of_continuous
    (f := (MulSemiringAction.toRingHom (A.decompositionSubgroup F) (WithVal A.valuation) σ :
      WithVal A.valuation →+ WithVal A.valuation)) (continuous_smul_withVal h.out σ)⟩

section Completion

variable [h : Fact (A.DecompositionIsometric F)]


instance mulSemiringActionCompletion :
    MulSemiringAction (A.decompositionSubgroup F) A.valuation.Completion :=
  { (inferInstance : DistribMulAction (A.decompositionSubgroup F) A.valuation.Completion) with
    smul_one := fun σ => by
      rw [← Completion.coe_one, ← Completion.coe_smul, smul_one]
    smul_mul := fun σ x y =>
      Completion.induction_on₂ x y
        (isClosed_eq ((continuous_fst.fun_mul continuous_snd).fun_const_smul (σ : A.decompositionSubgroup F))
          ((continuous_fst.fun_const_smul (σ : A.decompositionSubgroup F)).fun_mul
            (continuous_snd.fun_const_smul (σ : A.decompositionSubgroup F))))
        fun a b => by simp only [← Completion.coe_mul, ← Completion.coe_smul, smul_mul'] }


end Completion

end ValuationSubring

end
