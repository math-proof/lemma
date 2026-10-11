import Mathlib
import sympy.Basic
import sympy.functions.special.log.Integral


/--
[Integral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Log/Integral.lean)
-/
@[path]
private lemma logarithmic_integral_zero_eq
-- given
  (hx : 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≠ (1 : ℝ)) :
-- imply
  Real.logarithmicIntegral ⟨(0 : ℝ), hx⟩ = 0 := by
-- proof
  apply Real.logarithmicIntegral_zero (hx := hx)

/--
[Integral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Log/Integral.lean)
-/
@[path]
private lemma logarithmic_integral_of_lt_one_eq
-- given
  (x : Real.LogarithmicIntegralDomain)
  (hx : x.val < 1) :
-- imply
  Real.logarithmicIntegral x = ∫ t in (0 : ℝ)..x.val, (Real.log t)⁻¹ := by
-- proof
  apply Real.logarithmicIntegral_of_lt_one (x := x) hx

/--
[Integral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Log/Integral.lean)
-/
@[path]
private lemma logarithmic_integral_of_one_lt_eq
-- given
  (x : Real.LogarithmicIntegralDomain)
  (hx : 1 < x.val) :
-- imply
  Real.logarithmicIntegral x =
    (∫ u in (0 : ℝ)..(1 : ℝ), ((Real.log (1 - u))⁻¹ + (Real.log (1 + u))⁻¹)) +
      ∫ t in (2 : ℝ)..x.val, (Real.log t)⁻¹ := by
-- proof
  apply Real.logarithmicIntegral_of_one_lt (x := x) hx


-- created on 2026-10-11
