import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7

universe u₁ u₂ u₃

open Pointwise

namespace AdicCompletion

variable (A : Type u₁) (B : Type u₂) [CommRing A] [CommRing B] [Algebra A B]
variable (G : Type u₃) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
variable (𝔓 : Ideal B)

noncomputable def stabAut (g : MulAction.stabilizer G 𝔓) :
    AdicCompletion 𝔓 B ≃ₐ[A] AdicCompletion 𝔓 B :=
  mapAlgEquiv 𝔓 𝔓 (MulSemiringAction.toAlgEquiv A B (g : G))
    (map_toAlgEquiv_le_of_mem_stabilizer A B G 𝔓 g)
    (by rw [toAlgEquiv_symm]
        exact map_toAlgEquiv_le_of_mem_stabilizer A B G 𝔓 g⁻¹)

noncomputable def stabilizerToCompletionAut :
    MulAction.stabilizer G 𝔓 →* (AdicCompletion 𝔓 B ≃ₐ[A] AdicCompletion 𝔓 B) where
  toFun := stabAut A B G 𝔓
  map_one' := by
    refine AlgEquiv.ext fun x => ext_evalₐ fun n => ?_
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (evalₐ 𝔓 n x)
    rw [evalₐ_stabAut A B G 𝔓 1 n x z hz, AlgEquiv.one_apply, ← hz,
      OneMemClass.coe_one, one_smul]
  map_mul' g₁ g₂ := by
    refine AlgEquiv.ext fun x => ext_evalₐ fun n => ?_
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (evalₐ 𝔓 n x)
    have h₂ : Ideal.Quotient.mk (𝔓 ^ n) ((g₂ : G) • z) =
        evalₐ 𝔓 n (stabAut A B G 𝔓 g₂ x) :=
      (evalₐ_stabAut A B G 𝔓 g₂ n x z hz).symm
    rw [AlgEquiv.mul_apply, evalₐ_stabAut A B G 𝔓 (g₁ * g₂) n x z hz,
      evalₐ_stabAut A B G 𝔓 g₁ n _ ((g₂ : G) • z) h₂, Subgroup.coe_mul, mul_smul]

@[reducible]
noncomputable def stabilizerMulSemiringAction :
    MulSemiringAction (MulAction.stabilizer G 𝔓) (AdicCompletion 𝔓 B) :=
  MulSemiringAction.compHom _ (stabilizerToCompletionAut A B G 𝔓)

end AdicCompletion

#check @AdicCompletion.stabilizerMulSemiringAction
#check @AdicCompletion.stabilizerToCompletionAut
#print axioms AdicCompletion.smul_mem_of_mem_stabilizer
#print axioms AdicCompletion.map_toAlgEquiv_le_of_mem_stabilizer
#print axioms AdicCompletion.toAlgEquiv_symm
#print axioms AdicCompletion.stabAut
#print axioms AdicCompletion.evalₐ_stabAut
#print axioms AdicCompletion.stabilizerToCompletionAut
#print axioms AdicCompletion.stabilizerMulSemiringAction
#print axioms AdicCompletion.stabilizerToCompletionAut_of
