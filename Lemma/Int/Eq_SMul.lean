import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Bialgebra_exists_bialgEquiv_cancelBaseChange_tmul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Bialgebra_exists_bialgEquiv_cancelBaseChange_tmul.lean)
-/
@[path]
private lemma main
  (R R' S : Type u) [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R' S] [Algebra R S]
  [IsScalarTower R R' S]
  (C : Type u) [CommRing C] [Bialgebra R C] :
  -- imply
  ∃ e : BialgEquiv S (S ⊗[R'] (R' ⊗[R] C)) (S ⊗[R] C), ∀ (s : S) (r : R') (c : C), e (s ⊗ₜ (r ⊗ₜ c)) = (r • s) ⊗ₜ c := by
  -- proof
  classical
  let e₀ : AlgEquiv S (S ⊗[R'] (R' ⊗[R] C)) (S ⊗[R] C) := Algebra.TensorProduct.cancelBaseChange R R' S S C
  have he₀ : ∀ (s : S) (r : R') (c : C), e₀ (s ⊗ₜ (r ⊗ₜ c)) = (r • s) ⊗ₜ c := fun s r c =>
    Algebra.TensorProduct.cancelBaseChange_tmul R R' S S C s r c
  have he₁ : ∀ c : C, e₀ ((1 : S) ⊗ₜ ((1 : R') ⊗ₜ c)) = (1 : S) ⊗ₜ c := fun c => by
    rw [he₀, one_smul]
  refine ⟨BialgEquiv.ofAlgEquiv e₀ ?_ ?_, he₀⟩
  ·
    apply Algebra.TensorProduct.ext
    · ext
    ·
      apply Algebra.TensorProduct.ext
      · ext
      ·
        ext c
        simp [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply, Algebra.TensorProduct.includeRight_apply, Bialgebra.counitAlgHom_apply]
        rw [he₁]
        simp [TensorProduct.counit_tmul, Algebra.algebraMap_eq_smul_one]
  ·
    apply Algebra.TensorProduct.ext
    · ext
    ·
      apply Algebra.TensorProduct.ext
      · ext
      ·
        ext c
        simp [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply, Algebra.TensorProduct.includeRight_apply, Bialgebra.comulAlgHom_apply]
        rw [he₁]
        let 𝓡 := Coalgebra.Repr.arbitrary R c
        have hc : Coalgebra.comul (R := R) c = 𝓡.index.sum fun i => 𝓡.left i ⊗ₜ[R] 𝓡.right i := 𝓡.eq.symm
        simp [TensorProduct.comul_tmul, CommSemiring.comul_apply, hc, TensorProduct.tmul_sum, map_sum, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.map_tmul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [he₁]


-- created on 2026-10-20
