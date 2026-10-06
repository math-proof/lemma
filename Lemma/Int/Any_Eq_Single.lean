import Mathlib
import sympy.Basic

open scoped TensorProduct

/--
[AddMonoidAlgebra_exists_bialgEquiv_baseChange_tmul_single](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddMonoidAlgebra_exists_bialgEquiv_baseChange_tmul_single.lean)
-/
@[main]
private lemma main
  [AddCommMonoid G]
  {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
-- imply
  ∃ e : S ⊗[R] AddMonoidAlgebra R G ≃ₐc[S] AddMonoidAlgebra S G,
      ∀ (s : S) (g : G) (r : R), e (s ⊗ₜ AddMonoidAlgebra.single g r) = AddMonoidAlgebra.single g (r • s) := by
-- proof
  classical
  let e₀ : S ⊗[R] AddMonoidAlgebra R G ≃ₐ[S] AddMonoidAlgebra S G := AddMonoidAlgebra.scalarTensorEquiv R S
  have he₀ : ∀ (s : S) (g : G) (r : R), e₀ (s ⊗ₜ AddMonoidAlgebra.single g r) = AddMonoidAlgebra.single g (r • s) := by
    intro s g r
    simp only [e₀, AddMonoidAlgebra.scalarTensorEquiv_tmul, AddMonoidAlgebra.mapAlgHom_single, Algebra.ofId_apply,
      Algebra.smul_def, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.single_mul_single,
      zero_add, Algebra.algebraMap_self, RingHom.id_apply, mul_comm s]
  have he₁ : ∀ g : G, e₀ (1 ⊗ₜ AddMonoidAlgebra.single g 1) = AddMonoidAlgebra.single g 1 := fun g => by
    simpa using he₀ 1 g 1
  refine ⟨BialgEquiv.ofAlgEquiv e₀ ?_ ?_, he₀⟩
  · apply Algebra.TensorProduct.ext
    · ext
    · refine AddMonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
      simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
        Algebra.TensorProduct.includeRight_apply, AlgEquiv.coe_algHom, Bialgebra.counitAlgHom_apply]
      rw [he₁]
      simp [AddMonoidAlgebra.counit_single]
  · apply Algebra.TensorProduct.ext
    · ext
    · refine AddMonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
      simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
        Algebra.TensorProduct.includeRight_apply, AlgEquiv.coe_algHom, Bialgebra.comulAlgHom_apply]
      rw [he₁]
      simp [AddMonoidAlgebra.comul_single, CommSemiring.comul_apply, he₁]


-- created on 2026-10-05
