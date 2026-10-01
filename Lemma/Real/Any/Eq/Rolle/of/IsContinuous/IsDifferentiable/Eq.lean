import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (h : a < b)
  (hc : ContinuousOn f (Set.Icc a b))
  (_hd : DifferentiableOn ℝ f (Set.Ioo a b))
  (he : f a = f b) :
-- imply
  ∃ z ∈ Set.Ioo a b, deriv f z = 0 := by
-- proof
  exact exists_deriv_eq_zero h hc he


-- created on 2020-06-16
