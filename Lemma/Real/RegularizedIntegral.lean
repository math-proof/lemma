import Mathlib
import sympy.Basic
import sympy.functions.special.gamma.RegularizedIntegral


/--
[RegularizedIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Gamma/RegularizedIntegral.lean)
-/
@[path]
private lemma interval_integrable_exp_neg_sub_one_div_is :
-- imply
  IntervalIntegrable (fun t : ℝ => (((Real.exp (-t) - 1) / t : ℝ) : ℂ)) MeasureTheory.volume 0 1 := by
-- proof
  apply Real.intervalIntegrable_exp_neg_sub_one_div

/--
[RegularizedIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Gamma/RegularizedIntegral.lean)
-/
@[path]
private lemma euler_mascheroni_constant_eq_regularized_integrals_eq :
-- imply
  (Real.eulerMascheroniConstant : ℂ) =
    (∫ t : ℝ in 0..1, (((1 - Real.exp (-t)) / t : ℝ) : ℂ)) -
      ∫ t : ℝ in Set.Ioi 1, ((Real.exp (-t) / t : ℝ) : ℂ) := by
-- proof
  apply Real.eulerMascheroniConstant_eq_regularized_integrals


-- created on 2026-10-11
