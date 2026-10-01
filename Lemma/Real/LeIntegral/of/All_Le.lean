import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {f g : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hab : a ≤ b)
  (hf : IntervalIntegrable f MeasureTheory.volume a b)
  (hg : IntervalIntegrable g MeasureTheory.volume a b)
  (h : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
-- imply
  ∫ x in a..b, f x ≤ ∫ x in a..b, g x := by
-- proof
  exact intervalIntegral.integral_mono_on hab hf hg h


-- created on 2019-01-25
