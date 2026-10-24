import Lemma.Definitions.Def_AdicCompletionRingFunctoriality

universe u₁ u₂ u₃

open Pointwise

namespace AdicCompletion

variable (A : Type u₁) (B : Type u₂) [CommRing A] [CommRing B] [Algebra A B]
variable (G : Type u₃) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
variable (𝔓 : Ideal B)

theorem smul_mem_of_mem_stabilizer (g : MulAction.stabilizer G 𝔓) {x : B} (hx : x ∈ 𝔓) :
    (g : G) • x ∈ 𝔓 := by
  have h : (g : G) • 𝔓 = 𝔓 := g.2
  have hmem : (g : G) • x ∈ (g : G) • 𝔓 := by
    rw [Ideal.pointwise_smul_def]
    exact Ideal.mem_map_of_mem _ hx
  rwa [h] at hmem

theorem map_toAlgEquiv_le_of_mem_stabilizer (g : MulAction.stabilizer G 𝔓) :
    𝔓.map (MulSemiringAction.toAlgEquiv A B (g : G) : B →ₐ[A] B) ≤ 𝔓 :=
  Ideal.map_le_iff_le_comap.mpr fun _ hx => smul_mem_of_mem_stabilizer B G 𝔓 g hx

theorem toAlgEquiv_symm (g : G) :
    (MulSemiringAction.toAlgEquiv A B g).symm = MulSemiringAction.toAlgEquiv A B g⁻¹ := by
  ext b
  rw [AlgEquiv.symm_apply_eq]
  show b = g • g⁻¹ • b
  rw [smul_inv_smul]

noncomputable def stabAut (g : MulAction.stabilizer G 𝔓) :
    AdicCompletion 𝔓 B ≃ₐ[A] AdicCompletion 𝔓 B :=
  mapAlgEquiv 𝔓 𝔓 (MulSemiringAction.toAlgEquiv A B (g : G))
    (map_toAlgEquiv_le_of_mem_stabilizer A B G 𝔓 g)
    (by rw [toAlgEquiv_symm]
        exact map_toAlgEquiv_le_of_mem_stabilizer A B G 𝔓 g⁻¹)

theorem evalₐ_stabAut (g : MulAction.stabilizer G 𝔓) (n : ℕ) (x : AdicCompletion 𝔓 B)
    (z : B) (hz : Ideal.Quotient.mk (𝔓 ^ n) z = evalₐ 𝔓 n x) :
    evalₐ 𝔓 n (stabAut A B G 𝔓 g x) = Ideal.Quotient.mk (𝔓 ^ n) ((g : G) • z) := by
  rw [stabAut, mapAlgEquiv_apply, evalₐ_mapₐ, ← hz, levelMapₐ_mk]
  rfl

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

@[simp]
theorem stabilizerToCompletionAut_of (g : MulAction.stabilizer G 𝔓) (b : B) :
    stabilizerToCompletionAut A B G 𝔓 g (of 𝔓 B b) = of 𝔓 B ((g : G) • b) := by
  show stabAut A B G 𝔓 g (of 𝔓 B b) = _
  rw [stabAut, mapAlgEquiv_apply, mapₐ_of]
  rfl

end AdicCompletion

set_option pp.universes true in
#check @AdicCompletion.stabilizerMulSemiringAction
set_option pp.universes true in
#check @AdicCompletion.stabilizerToCompletionAut
#print axioms AdicCompletion.smul_mem_of_mem_stabilizer
#print axioms AdicCompletion.map_toAlgEquiv_le_of_mem_stabilizer
#print axioms AdicCompletion.toAlgEquiv_symm
#print axioms AdicCompletion.stabAut
#print axioms AdicCompletion.evalₐ_stabAut
#print axioms AdicCompletion.stabilizerToCompletionAut
#print axioms AdicCompletion.stabilizerMulSemiringAction
#print axioms AdicCompletion.stabilizerToCompletionAut_of
