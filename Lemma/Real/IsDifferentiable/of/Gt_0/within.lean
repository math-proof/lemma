import Mathlib.Analysis.Calculus.Deriv.Basic
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (h₀ : ∀ x ∈ Set.Ioo a b, 0 < deriv (deriv f) x) :
-- imply
  ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ (deriv f) x := by
-- proof
  intro x hx
  apply differentiableAt_of_deriv_ne_zero
  apply (h₀ x hx).ne'


-- created on 2020-05-06
-- updated on 2026-10-17
