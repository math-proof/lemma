import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {f : ℝ → ℝ}
  {a b c : ℝ}
-- given
  (hab : IntervalIntegrable f MeasureTheory.volume a b)
  (hac : IntervalIntegrable f MeasureTheory.volume a c) :
-- imply
  (∫ x in a..b, f x) - ∫ x in a..c, f x = ∫ x in c..b, f x := by
-- proof
  exact intervalIntegral.integral_interval_sub_left hab hac


-- created on 2026-09-27
