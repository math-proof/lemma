import Mathlib
import sympy.Basic

open scoped TensorProduct

/--
[Algebra_norm_one_tmul_eq_algebraMap_norm](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_norm_one_tmul_eq_algebraMap_norm.lean)
-/
@[main]
private lemma main
  {K : Type u} [CommRing K]
  {L : Type v} [Ring L] [Algebra K L] [Module.Free K L] [Module.Finite K L]
  {K' : Type w} [CommRing K'] [Algebra K K']
  {x : L} :
-- imply
  Algebra.norm K' ((1 : K') ⊗ₜ[K] x : K' ⊗[K] L) = algebraMap K K' (Algebra.norm K x) := by
-- proof
  classical
    rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
    congr 1
    apply LinearMap.ext
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c l => simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    | add y z hy hz => simp only [map_add, hy, hz]


-- created on 2026-10-05
