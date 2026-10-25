/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/PowerGrowthBadSet.lean -/

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-!
# Power-growth exceptional sets

This file proves that the points where a positive monotone smooth real function grows at
least as fast as a fixed power greater than one form a set of finite Lebesgue measure.
-/


namespace Real

open Filter MeasureTheory Set

open scoped ENNReal Interval

/-- The log-radius points where a positive function grows at least as fast as
the prescribed power of its current value. -/
def powerGrowthBadSet (h : ℝ → ℝ) (p x₀ : ℝ) : Set ℝ :=
  {x | x₀ ≤ x ∧ h x ^ p ≤ deriv h x}

end Real
