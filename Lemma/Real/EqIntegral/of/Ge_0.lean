import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma limits.offset
  {f : ℝ → ℝ}
  {a b d : ℝ}
-- given
  (_h : ∀ x, f x ≥ 0) :
-- imply
  ∫ x in a..b, f x = ∫ x in (a - d)..(b - d), f (x + d) := by
-- proof
  rw [intervalIntegral.integral_comp_add_right, sub_add_cancel, sub_add_cancel]


-- created on 2026-09-27
