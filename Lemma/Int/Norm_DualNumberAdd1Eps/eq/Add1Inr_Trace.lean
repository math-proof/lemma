import Mathlib
import sympy.Basic

open scoped TensorProduct

/--
[Algebra_norm_one_add_eps_tmul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_norm_one_add_eps_tmul.lean)
-/
@[path]
private lemma main
  {A' B : Type u} [CommRing A'] [CommRing B] [Algebra A' B] [Module.Free A' B] [Module.Finite A' B]
  {f : B} :
-- imply
  Algebra.norm (DualNumber A') ((1 : DualNumber A' ⊗[A'] B) + (DualNumber.eps : DualNumber A') ⊗ₜ[A'] f) =
      1 + TrivSqZeroExt.inr (Algebra.trace A' B f) := by
-- proof
  classical
  let b := Module.Free.chooseBasis A' B
  let b' : Module.Basis (Module.Free.ChooseBasisIndex A' B) (DualNumber A') (DualNumber A' ⊗[A'] B) :=
    Algebra.TensorProduct.basis (DualNumber A') b
  have hM : ∀ g : B, Algebra.leftMulMatrix b' ((1 : DualNumber A') ⊗ₜ[A'] g)
      = (Algebra.leftMulMatrix b g).map (algebraMap A' (DualNumber A')) := by
    intro g
    have hlmul : Algebra.lmul (DualNumber A') (DualNumber A' ⊗[A'] B) ((1 : DualNumber A') ⊗ₜ[A'] g)
        = (Algebra.lmul A' B g).baseChange (DualNumber A') := by
      apply b'.ext
      intro k
      simp [b', Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
    rw [Algebra.leftMulMatrix_apply, hlmul, LinearMap.toMatrix_baseChange, Algebra.leftMulMatrix_apply]
  have hone : Algebra.leftMulMatrix (R := DualNumber A') (S := DualNumber A' ⊗[A'] B) b' 1 = 1 := by
    rw [Algebra.TensorProduct.one_def, hM 1, map_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : (DualNumber.eps : DualNumber A') ⊗ₜ[A'] f
      = (DualNumber.eps : DualNumber A') • ((1 : DualNumber A') ⊗ₜ[A'] f) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hadd : Algebra.leftMulMatrix b' ((1 : DualNumber A' ⊗[A'] B) + (DualNumber.eps : DualNumber A') ⊗ₜ[A'] f)
      = 1 + (DualNumber.eps : DualNumber A') • (Algebra.leftMulMatrix b f).map (algebraMap A' (DualNumber A')) := by
    rw [h1]
    simp only [map_add, map_smul, hone, hM]
  rw [Algebra.norm_eq_matrix_det b', hadd, Matrix.det_one_add_smul,
    pow_two, DualNumber.eps_mul_eps, mul_zero, add_zero,
    ← AddMonoidHom.map_trace (algebraMap A' (DualNumber A')), ← Algebra.trace_eq_matrix_trace b f]
  congr 1
  rw [TrivSqZeroExt.algebraMap_eq_inl, DualNumber.eps, TrivSqZeroExt.inl_mul_inr, smul_eq_mul,
    mul_one]


-- created on 2026-10-05
