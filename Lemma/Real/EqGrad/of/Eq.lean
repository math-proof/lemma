import Mathlib.Analysis.Calculus.Deriv.MeanValue
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {f g : ℝ → ℝ}
  {x : ℝ}
-- given
  (h : ∀ x, f x = g x) :
-- imply
  deriv f x = deriv g x := by
-- proof
  rw [funext h]


-- created on 2020-10-17
