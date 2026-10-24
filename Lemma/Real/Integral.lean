import Mathlib
import sympy.Basic
import sympy.functions.special.log.Integral


namespace Real

/--
[Integral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Log/Integral.lean)
-/
@[path]
lemma logarithmicIntegral_zero
-- given
  (hx : 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≠ (1 : ℝ)) :
-- imply
  Real.logarithmicIntegral ⟨(0 : ℝ), hx⟩ = 0 := by
-- proof
  simp [logarithmicIntegral]

end Real

namespace Real

/--
[Integral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Log/Integral.lean)
-/
@[path]
lemma logarithmicIntegral_of_lt_one
-- given
  (x : Real.LogarithmicIntegralDomain)
  (hx : x.val < 1) :
-- imply
  Real.logarithmicIntegral x = ∫ t in (0 : ℝ)..x.val, (Real.log t)⁻¹ := by
-- proof
  simp [logarithmicIntegral, hx]

end Real

namespace Real

/--
[Integral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Log/Integral.lean)
-/
@[path]
lemma logarithmicIntegral_of_one_lt
-- given
  (x : Real.LogarithmicIntegralDomain)
  (hx : 1 < x.val) :
-- imply
  Real.logarithmicIntegral x =
    (∫ u in (0 : ℝ)..(1 : ℝ), ((Real.log (1 - u))⁻¹ + (Real.log (1 + u))⁻¹)) +
      ∫ t in (2 : ℝ)..x.val, (Real.log t)⁻¹ := by
-- proof
  have h : ¬ x.val < 1 := not_lt.mpr hx.le
  simp [logarithmicIntegral, h]

end Real


-- created on 2020-06-09
-- updated on 2026-10-23
