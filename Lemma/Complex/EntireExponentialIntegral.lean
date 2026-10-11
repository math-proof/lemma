import Mathlib
import sympy.Basic
import sympy.functions.special.EntireExponentialIntegral


/--
[EntireExponentialIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/EntireExponentialIntegral.lean)
-/
@[path]
private lemma has_deriv_at_ein_is
-- given
  (z : ℂ) :
-- imply
  HasDerivAt Complex.ein
    (∑' n : ℕ, (-1 : ℂ) ^ n * z ^ n / ((n + 1).factorial : ℂ)) z := by
-- proof
  apply Complex.hasDerivAt_ein z

/--
[EntireExponentialIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/EntireExponentialIntegral.lean)
-/
@[path]
private lemma differentiable_ein_is :
-- imply
  Differentiable ℂ Complex.ein := by
-- proof
  apply Complex.differentiable_ein

/--
[EntireExponentialIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/EntireExponentialIntegral.lean)
-/
@[path]
private lemma analytic_on_nhd_ein_is :
-- imply
  AnalyticOnNhd ℂ Complex.ein Set.univ := by
-- proof
  apply Complex.analyticOnNhd_ein

/--
[EntireExponentialIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/EntireExponentialIntegral.lean)
-/
@[path]
private lemma mul_deriv_ein_eq
-- given
  (z : ℂ) :
-- imply
  z * deriv Complex.ein z = 1 - Complex.exp (-z) := by
-- proof
  apply Complex.mul_deriv_ein z


-- created on 2026-10-11
