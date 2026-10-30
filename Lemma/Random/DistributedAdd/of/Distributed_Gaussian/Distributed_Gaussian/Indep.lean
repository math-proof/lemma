import Mathlib.Probability.Distributions.Gaussian.Real
import Notation.Probability.HasLaw
import Notation.Algebra.Power
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory
open scoped NNReal


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x₀ x₁ : Ω → ℝ}
  {μ₀ μ₁ : ℝ} {σ₀ σ₁ : NNReal}
-- given
  (h₀ : x₀ ⟂ᵢ[π] x₁)
  (h₁ : x₀ ∼[π] gaussianReal μ₀ σ₀²)
  (h₂ : x₁ ∼[π] gaussianReal μ₁ σ₁²) :
-- imply
  x₀ + x₁ ∼[π] gaussianReal (μ₀ + μ₁) (σ₀² + σ₁²) := by
-- proof
  refine ⟨h₁.aemeasurable.add h₂.aemeasurable, ?_⟩
  apply gaussianReal_add_gaussianReal_of_indepFun h₀ h₁ h₂


-- created on 2021-07-25
-- updated on 2026-10-29
