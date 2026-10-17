import Mathlib.Probability.Distributions.Gaussian.Real
import sympy.Basic
open MeasureTheory ProbabilityTheory
open scoped NNReal


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x y : Ω → ℝ}
  {μ₀ μ₁ : ℝ} {v₀ v₁ : ℝ≥0}
-- given
  (h₀ : x ⟂ᵢ[π] y)
  (h₁ : HasLaw x (gaussianReal μ₀ v₀) π)
  (h₂ : HasLaw y (gaussianReal μ₁ v₁) π) :
-- imply
  π.map (x + y) = gaussianReal (μ₀ + μ₁) (v₀ + v₁) :=
-- proof
  gaussianReal_add_gaussianReal_of_indepFun h₀ h₁ h₂


-- created on 2023-05-03
-- updated on 2026-10-17
