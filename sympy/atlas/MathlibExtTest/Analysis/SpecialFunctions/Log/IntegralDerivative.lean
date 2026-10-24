/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/Log/IntegralDerivative.lean -/


import sympy.atlas.Analysis.SpecialFunctions.Log.IntegralDerivative
import Lemma.Real.SpecialFunctions.Log.IntegralDerivative

/-!
# Tests for the logarithmic integral derivative bridge
-/

namespace Real

example (x : ℝ) (h : 0 ≤ x ∧ x ≠ 1) :
    Real.logarithmicIntegralReal x =
      Real.logarithmicIntegral (⟨x, h⟩ : Real.LogarithmicIntegralDomain) :=
  Real.logarithmicIntegralReal_of_mem h

example : Real.logarithmicIntegralReal (0.5 : ℝ) =
    ∫ t in (0 : ℝ)..(0.5 : ℝ), (Real.log t)⁻¹ := by
  have : (0 : ℝ) ≤ 0.5 := by norm_num
  exact Real.logarithmicIntegralReal_of_lt_one this (by norm_num)

example : Real.logarithmicIntegralReal (3 : ℝ) =
    (∫ u in (0 : ℝ)..(1 : ℝ), ((Real.log (1 - u))⁻¹ + (Real.log (1 + u))⁻¹)) +
      ∫ t in (2 : ℝ)..(3 : ℝ), (Real.log t)⁻¹ := by
  rw [Real.logarithmicIntegralReal_of_one_lt (by norm_num : (1 : ℝ) < 3)]

example : Real.logarithmicIntegralReal 1 = 0 := by
  simp [Real.logarithmicIntegralReal]

example : Real.logarithmicIntegralReal 0 = 0 :=
  Real.logarithmicIntegralReal_zero


example {x : ℝ} (hx_pos : 0 < x) (hx_ne_one : x ≠ 1) :
    HasDerivAt Real.logarithmicIntegralReal (1 / Real.log x) x :=
  Real.hasDerivAt_logarithmicIntegralReal hx_pos hx_ne_one

example : HasDerivAt Real.logarithmicIntegralReal (1 / Real.log 0.5) (0.5 : ℝ) :=
  Real.hasDerivAt_logarithmicIntegralReal (by norm_num) (by norm_num)

example : HasDerivAt Real.logarithmicIntegralReal (1 / Real.log 3) (3 : ℝ) :=
  Real.hasDerivAt_logarithmicIntegralReal (by norm_num) (by norm_num)

#print axioms Real.hasDerivAt_logarithmicIntegralReal

end Real
