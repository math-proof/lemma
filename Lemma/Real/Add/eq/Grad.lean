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
  deriv f x - deriv g x = deriv (fun t ↦ f t - g t) x := by
-- proof
  rw [show (fun t ↦ f t - g t) = f - g from rfl]
  rw [deriv_sub hf hg]


-- created on 2026-10-07
