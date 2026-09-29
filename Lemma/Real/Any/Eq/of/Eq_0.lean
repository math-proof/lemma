import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma constant_fn
  {f : ℝ → ℝ}
-- given
  (hd : Differentiable ℝ f)
  (h : ∀ x, deriv f x = 0) :
-- imply
  ∃ C, ∀ x, f x = C := by
-- proof
  exact ⟨f 0, fun x => is_const_of_deriv_eq_zero hd h x 0⟩


-- created on 2026-09-27
