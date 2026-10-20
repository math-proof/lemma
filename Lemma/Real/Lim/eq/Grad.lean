import Mathlib.Analysis.Calculus.Deriv.Slope
import sympy.series.limits
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x : ℝ}
-- given
  (h₀ : DifferentiableAt ℝ f x) :
-- imply
  lim [y → x] slope f x y = deriv f x :=
-- proof
  h₀.hasDerivAt.tendsto_slope


-- created on 2023-06-22
-- updated on 2026-10-17
