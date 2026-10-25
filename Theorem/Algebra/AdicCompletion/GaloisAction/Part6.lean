import Mathlib
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Def.Algebra.AdicCompletion.GaloisAction.Part5
set_option autoImplicit false

open scoped Pointwise


namespace AdicCompletion.GaloisAction

end AdicCompletion.GaloisAction

namespace AdicCompletion

open scoped AdicCompletion.GaloisAction

universe u v w

variable {C : Type u} [CommRing C] {G : Type v} [Group G] [MulSemiringAction G C]

section LiesOver

variable {O : Type w} [CommRing O] [Algebra O C] (J : Ideal O) (𝔫 : Ideal C)

theorem algebraMap_eq_algHomOfLiesOver [𝔫.LiesOver J] (x : AdicCompletion J O) :
    algebraMap (AdicCompletion J O) (AdicCompletion 𝔫 C) x = algHomOfLiesOver J 𝔫 x :=
  rfl

theorem instIsScalarTowerOfLiesOver [𝔫.LiesOver J] :
    IsScalarTower O (AdicCompletion J O) (AdicCompletion 𝔫 C) :=
  IsScalarTower.of_algebraMap_eq fun o =>
    (AlgHom.commutes (algHomOfLiesOver J 𝔫) o).symm

scoped[AdicCompletion.GaloisAction] attribute [instance] AdicCompletion.instIsScalarTowerOfLiesOver

@[simp]
theorem algebraMap_of [𝔫.LiesOver J] (o : O) :
    algebraMap (AdicCompletion J O) (AdicCompletion 𝔫 C) (of J O o) = of 𝔫 C (algebraMap O C o) := by
  rw [algebraMap_eq_algHomOfLiesOver, algHomOfLiesOver, mapₐ_of]
  rfl

theorem evalₐ_algebraMap_of_liesOver [𝔫.LiesOver J] (n : ℕ) (o : O) (x : AdicCompletion J O)
    (hx : evalₐ J n x = Ideal.Quotient.mk (J ^ n) o) :
    evalₐ 𝔫 n (algebraMap (AdicCompletion J O) (AdicCompletion 𝔫 C) x)
      = Ideal.Quotient.mk (𝔫 ^ n) (algebraMap O C o) := by
  rw [algebraMap_eq_algHomOfLiesOver, algHomOfLiesOver, evalₐ_mapₐ, hx, levelMapₐ_mk]
  rfl

theorem stabilizer_smul_algebraMap [SMulCommClass G O C] [𝔫.LiesOver J]
    (d : MulAction.stabilizer G 𝔫) (a : AdicCompletion J O) :
    d • algebraMap (AdicCompletion J O) (AdicCompletion 𝔫 C) a
      = algebraMap (AdicCompletion J O) (AdicCompletion 𝔫 C) a := by
  apply ext_evalₐ
  intro n
  obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective (evalₐ J n a)
  rw [evalₐ_stabilizer_smul 𝔫 d n (algebraMap O C o) _ (evalₐ_algebraMap_of_liesOver J 𝔫 n o a ho.symm),
    evalₐ_algebraMap_of_liesOver J 𝔫 n o a ho.symm, smul_algebraMap_eq]

theorem instSMulCommClassStabilizerOfLiesOver [SMulCommClass G O C] [𝔫.LiesOver J] :
    SMulCommClass (MulAction.stabilizer G 𝔫) (AdicCompletion J O) (AdicCompletion 𝔫 C) where
  smul_comm d a x := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', stabilizer_smul_algebraMap]

scoped[AdicCompletion.GaloisAction] attribute [instance] AdicCompletion.instSMulCommClassStabilizerOfLiesOver

end LiesOver
end AdicCompletion
