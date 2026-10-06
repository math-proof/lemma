import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import sympy.Basic


open MeasureTheory


@[main]
private lemma main
  {f : ℝ → ℝ}
  {a b c : ℝ}
-- given
  (hab : IntervalIntegrable f volume a b)
  (hbc : IntervalIntegrable f volume b c) :
-- imply
  ∫ x in a..c, f x = (∫ x in a..b, f x) + ∫ x in b..c, f x :=
-- proof
  (intervalIntegral.integral_add_adjacent_intervals hab hbc).symm


-- created on 2023-03-21
