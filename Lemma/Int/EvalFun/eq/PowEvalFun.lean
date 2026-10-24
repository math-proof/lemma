import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Lemma.Int.P2MUtil

open AlgebraicCurve AlgebraicCurve.Divisor

/--
[AlgebraicCurve_Divisor_evalFun_zsmul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Divisor_evalFun_zsmul.lean)
-/
@[path]
private lemma main
  {K F : Type*} [Field K] [Field F] [Algebra K F]
  {f : F}
  {D : Divisor K F}
  {n : ℤ} :
-- imply
  Divisor.evalFun f (n • D) = Divisor.evalFun f D ^ n := by
-- proof
  rw [show evalFun f (n • D) = ∏ v ∈ D.support, v.evalAt f ^ ((n • D) v) from
      Finsupp.prod_of_support_subset _ Finsupp.support_smul _ fun v _ => zpow_zero _,
    evalFun_def, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, mul_comm n (D v), zpow_mul]


-- created on 2026-10-23
