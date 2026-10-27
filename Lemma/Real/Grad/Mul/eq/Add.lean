import Mathlib.Analysis.Calculus.Deriv.Mul
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f g : ℝ → ℝ}
  {x : ℝ}
-- given
  (h₀ : DifferentiableAt ℝ f x)
  (h₁ : DifferentiableAt ℝ g x) :
-- imply
  deriv (f * g) x = deriv f x * g x + f x * deriv g x :=
-- proof
  (h₀.hasDerivAt.mul h₁.hasDerivAt).deriv


-- created on 2022-01-19
-- updated on 2026-10-26
