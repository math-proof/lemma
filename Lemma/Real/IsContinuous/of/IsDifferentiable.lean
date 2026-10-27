import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (h : DifferentiableOn ℝ f (Set.Icc a b)) :
-- imply
  ContinuousOn f (Set.Icc a b) := by
-- proof
  exact h.continuousOn


-- created on 2020-04-18
