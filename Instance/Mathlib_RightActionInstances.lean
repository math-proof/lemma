-- Carved from Lemma/Definitions/Def_Mathlib_RightActionInstances.lean: instance decls only.
import Mathlib
import Def.Mathlib_RightActionInstances

section

namespace TensorProduct.RightActions

noncomputable section semiring

variable (R S A B M : Type*) [CommSemiring R] [CommSemiring S] [AddCommMonoid M]

scoped instance : SMul S (M ⊗[R] S) where
  smul s e := TensorProduct.comm _ _ _ (s • (TensorProduct.comm _ _ _ e))

scoped instance : Module S (M ⊗[R] S) where
  one_smul x := by simp_rw [smul_def, one_smul, (TensorProduct.comm R M S).symm_apply_apply]
  mul_smul a b x := by simp_rw [smul_def, mul_smul, (TensorProduct.comm R M S).apply_symm_apply]
  smul_zero := by simp
  smul_add := by simp
  add_smul := by simp [add_smul]
  zero_smul := by simp

scoped instance : Algebra S (B ⊗[R] S) where
  algebraMap := Algebra.TensorProduct.includeRight.toRingHom
  commutes' s bs := by
    induction bs using TensorProduct.induction_on with
    | zero => simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, mul_zero, zero_mul]
    | tmul x y =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          mul_one, mul_comm]
    | add x y _ _ =>
        simp_all only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, mul_add, add_mul]
  smul_def' s bs := by
    induction bs using TensorProduct.induction_on with
    | zero => simp only [smul_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, mul_zero]
    | tmul b s =>
        simp only [smul_def, TensorProduct.comm_tmul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rw [TensorProduct.smul_tmul']
        simp only [smul_eq_mul, TensorProduct.comm_symm_tmul]
    | add x y hx hy =>
        simp_all only [smul_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, smul_add, mul_add]

scoped instance [Module.Finite R M] : Module.Finite A (M ⊗[R] A) :=
  Module.Finite.equiv (Module.TensorProduct.comm R A M)

scoped instance [Module.Free R M] : Module.Free A (M ⊗[R] A) :=
  Module.Free.of_equiv (Module.TensorProduct.comm R A M)

scoped instance : IsScalarTower R A (M ⊗[R] A) where
  smul_assoc r a ma := by simp

@[nolint unusedArguments]

scoped instance [TopologicalSpace A] [Module.Finite R M] :
    TopologicalSpace (M ⊗[R] A) :=
  moduleTopology A (M ⊗[R] A)

scoped instance [TopologicalSpace A] [Module.Finite R M] :
  IsModuleTopology A (M ⊗[R] A) := ⟨rfl⟩

end semiring

noncomputable section ring

variable (R A B M : Type*) [CommRing R]

scoped instance [TopologicalSpace A] [Module.Finite R M] :
    IsTopologicalAddGroup (M ⊗[R] A) := IsModuleTopology.topologicalAddGroup A (M ⊗[R] A)

end ring

end TensorProduct.RightActions
end
