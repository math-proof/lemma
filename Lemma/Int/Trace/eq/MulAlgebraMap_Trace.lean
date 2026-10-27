import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct


attribute [local instance] Algebra.TensorProduct.rightAlgebra

/--
[Algebra_trace_tensorProduct_rightActions_tmul_eq_algebraMap_trace_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_trace_tensorProduct_rightActions_tmul_eq_algebraMap_trace_mul.lean)
-/
@[path]
private lemma main
  {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  {A : Type} [CommRing A] [Algebra K A]
  {l : L}
  {a : A} :
-- imply
  Algebra.trace A (L ⊗[K] A) (l ⊗ₜ[K] a) =
    algebraMap K A (Algebra.trace K L l) * a := by
-- proof
  rw [← Algebra.trace_eq_of_algEquiv (Algebra.TensorProduct.commRight K A L).symm (l ⊗ₜ[K] a),
    Algebra.TensorProduct.commRight_symm_tmul]
  have hsmul : a ⊗ₜ[K] l = a • ((1 : A) ⊗ₜ[K] l) := by
    simp [Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul]
  rw [hsmul, map_smul, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, ← Algebra.trace_apply, Algebra.smul_def, mul_comm]
  simp


-- created on 2026-10-20
