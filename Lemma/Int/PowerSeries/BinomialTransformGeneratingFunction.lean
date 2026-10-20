import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.PowerSeries.BinomialTransformGeneratingFunction
open scoped BigOperators
open MetaMathlibExt


/--
[mk_sum_choose_mul_eq_inv_one_sub_mul_subst](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/BinomialTransformGeneratingFunction.lean)
-/
@[path]
private lemma mk_sum_choose_mul_eq_inv_one_sub_mul_subst_eq
  [Field K]
  {a : ℕ → K} :
-- imply
  PowerSeries.mk
    (fun n : ℕ =>
    ∑ k ∈ Finset.range (n + 1), (n.choose k : K) * a k) =
    (1 - (PowerSeries.X : PowerSeries K))⁻¹ *
    (PowerSeries.mk a).subst
    ((PowerSeries.X : PowerSeries K) * (1 - PowerSeries.X)⁻¹) := by
-- proof
  apply MetaMathlibExt.mk_sum_choose_mul_eq_inv_one_sub_mul_subst a

/--
[ordinary_generating_function_binomial_transform](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/BinomialTransformGeneratingFunction.lean)
-/
@[path]
private lemma ordinary_generating_function_binomial_transform_eq
  {a : ℕ → ℝ} :
-- imply
  PowerSeries.mk
    (fun n : ℕ =>
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a k) =
    (1 - (PowerSeries.X : PowerSeries ℝ))⁻¹ *
    (PowerSeries.mk a).subst
    ((PowerSeries.X : PowerSeries ℝ) * (1 - PowerSeries.X)⁻¹) := by
-- proof
  apply MetaMathlibExt.ordinary_generating_function_binomial_transform a


-- created on 2026-10-20
