import Mathlib.Analysis.Calculus.Deriv.Add
import sympy.Basic


@[main]
private lemma main
  {f g : ℝ → ℝ}
  {x : ℝ}
-- given
  (h₀ : DifferentiableAt ℝ f x)
  (h₁ : DifferentiableAt ℝ g x) :
-- imply
  deriv (fun x => f x + g x) x = deriv f x + deriv g x :=
-- proof
  deriv_add h₀ h₁


-- created on 2026-09-26
