import Mathlib
import sympy.Basic


@[main]
private lemma main
  {f g : ℝ → ℝ}
  {x : ℝ}
-- given
  (hf : DifferentiableAt ℝ f x)
  (hg : DifferentiableAt ℝ g x) :
-- imply
  deriv (fun x => f x * g x) x = deriv f x * g x + f x * deriv g x := by
-- proof
  exact deriv_mul hf hg


-- created on 2026-10-07
