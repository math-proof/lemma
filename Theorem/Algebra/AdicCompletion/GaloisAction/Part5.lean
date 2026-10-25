import Mathlib
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Def.Algebra.AdicCompletion.GaloisAction.Part4
set_option autoImplicit false

open scoped Pointwise


namespace AdicCompletion.GaloisAction

end AdicCompletion.GaloisAction

namespace AdicCompletion

open scoped AdicCompletion.GaloisAction

universe u v w

variable {C : Type u} [CommRing C] {G : Type v} [Group G] [MulSemiringAction G C]

section MapIdeal

variable {O : Type w} [CommRing O] [Algebra O C]

@[simp]
theorem map_smul_of [SMulCommClass G O C] (J : Ideal O) (g : G) (c : C) :
    g • of (J.map (algebraMap O C)) C c = of (J.map (algebraMap O C)) C (g • c) :=
  smul_of' _ (smul_map_algebraMap_eq J) g c

theorem evalₐ_map_smul [SMulCommClass G O C] (J : Ideal O) (g : G) (n : ℕ) (c : C)
    (x : AdicCompletion (J.map (algebraMap O C)) C)
    (hx : evalₐ (J.map (algebraMap O C)) n x = Ideal.Quotient.mk _ c) :
    evalₐ (J.map (algebraMap O C)) n (g • x) = Ideal.Quotient.mk _ (g • c) :=
  evalₐ_smul' _ (smul_map_algebraMap_eq J) g n c x hx

theorem instSMulCommClassStabilizer [SMulCommClass G O C] (𝔫 : Ideal C) :
    SMulCommClass (MulAction.stabilizer G 𝔫) O (AdicCompletion 𝔫 C) where
  smul_comm d o x := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', algebraMap_apply, stabilizer_smul_of,
      smul_algebraMap_eq]

scoped[AdicCompletion.GaloisAction] attribute [instance] AdicCompletion.instSMulCommClassStabilizer

theorem instSMulCommClassMap [SMulCommClass G O C] (J : Ideal O) :
    SMulCommClass G O (AdicCompletion (J.map (algebraMap O C)) C) where
  smul_comm g o x := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', algebraMap_apply, map_smul_of,
      smul_algebraMap_eq]

scoped[AdicCompletion.GaloisAction] attribute [instance] AdicCompletion.instSMulCommClassMap

end MapIdeal

section Faithful

theorem instFaithfulSMulStabilizer [FaithfulSMul G C] (𝔫 : Ideal C) [IsHausdorff 𝔫 C] :
    FaithfulSMul (MulAction.stabilizer G 𝔫) (AdicCompletion 𝔫 C) where
  eq_of_smul_eq_smul {d₁ d₂} h := by
    apply Subtype.ext
    apply eq_of_smul_eq_smul (α := C)
    intro c
    apply of_injective 𝔫 (M := C)
    rw [← stabilizer_smul_of, ← stabilizer_smul_of, h]

scoped[AdicCompletion.GaloisAction] attribute [instance] AdicCompletion.instFaithfulSMulStabilizer

end Faithful

section LiesOver

variable {O : Type w} [CommRing O] [Algebra O C] (J : Ideal O) (𝔫 : Ideal C)

theorem map_ofId_le_of_liesOver [h𝔫 : 𝔫.LiesOver J] : J.map (Algebra.ofId O C) ≤ 𝔫 := by
  rw [Ideal.map_le_iff_le_comap]
  intro o ho
  rw [h𝔫.over] at ho
  exact ho

end LiesOver
end AdicCompletion
