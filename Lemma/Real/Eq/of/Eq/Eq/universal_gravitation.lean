import Mathlib.Analysis.Calculus.Deriv.Mul
import sympy.Basic


@[path]
private lemma main
  {ρ u : ℝ → ℝ}
  {t : ℝ}
-- given
  (h₀ : DifferentiableAt ℝ ρ t)
  (h₁ : DifferentiableAt ℝ u t) :
-- imply
  deriv (fun s => ρ s * u s) t = deriv ρ t * u t + ρ t * deriv u t :=
-- proof
  (h₀.hasDerivAt.mul h₁.hasDerivAt).deriv


-- created on 2022-01-19
-- updated on 2026-10-17
