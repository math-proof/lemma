import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {f : ℝ → ℝ}
  {a b c : ℝ}
-- given
  (hab : IntervalIntegrable f MeasureTheory.volume a b)
  (hbc : IntervalIntegrable f MeasureTheory.volume b c) :
-- imply
  (∫ x in a..b, f x) + ∫ x in b..c, f x = ∫ x in a..c, f x :=
-- proof
  intervalIntegral.integral_add_adjacent_intervals hab hbc


-- created on 2026-10-08
