import Mathlib.Analysis.Calculus.Deriv.Comp
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f g : ℝ → ℝ}
  {x : ℝ}
-- given
  (h₀ : DifferentiableAt ℝ g x)
  (h₁ : DifferentiableAt ℝ f (g x)) :
-- imply
  deriv (f ∘ g) x = deriv f (g x) * deriv g x :=
-- proof
  deriv_comp x h₁ h₀


-- created on 2021-09-28
-- updated on 2026-10-26
