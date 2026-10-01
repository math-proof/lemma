import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {f g : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hf : IntervalIntegrable f MeasureTheory.volume a b)
  (hg : IntervalIntegrable g MeasureTheory.volume a b) :
-- imply
  (∫ x in a..b, f x) + ∫ x in a..b, g x = ∫ x in a..b, (f x + g x) := by
-- proof
  exact (intervalIntegral.integral_add hf hg).symm


@[main]
private lemma concat
  {f : ℝ → ℝ}
  {a b c : ℝ}
-- given
  (hab : IntervalIntegrable f MeasureTheory.volume a b)
  (hbc : IntervalIntegrable f MeasureTheory.volume b c) :
-- imply
  (∫ x in a..b, f x) + ∫ x in b..c, f x = ∫ x in a..c, f x := by
-- proof
  exact intervalIntegral.integral_add_adjacent_intervals hab hbc


-- created on 2026-09-27
