import Mathlib.Analysis.Calculus.Deriv.Basic
import sympy.series.limits
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x₀ : ℝ} :
-- imply
  deriv f x₀ = lim [x → x₀] ((f x - f x₀) / (x - x₀)) := by
-- proof
  sorry


-- created on 2026-10-11
