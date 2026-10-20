import Mathlib.Analysis.Calculus.Deriv.Inv
import sympy.Basic


@[path]
private lemma main
  {f g : ℝ → ℝ}
  {x : ℝ}
-- given
  (h₀ : DifferentiableAt ℝ f x)
  (h₁ : DifferentiableAt ℝ g x)
  (h₂ : g x ≠ 0) :
-- imply
  deriv (f / g) x = (deriv f x * g x - f x * deriv g x) / g x ^ 2 :=
-- proof
  (h₀.hasDerivAt.div h₁.hasDerivAt h₂).deriv


-- created on 2023-11-26
-- updated on 2026-10-17
