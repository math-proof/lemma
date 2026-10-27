import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.TheoryOfProbability.code.IntegrationProperties
open MeasureTheory


/--
[integration_properties](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/IntegrationProperties.lean)
-/
@[path]
lemma integration_properties
  [MeasurableSpace α]
  {μ : Measure α} :
-- imply
  (∀ f : α → ℝ, (0 ≤ᵐ[μ] f) → 0 ≤ ∫ x, f x ∂μ) ∧ (∀ (f g : α → ℝ) (a b : ℝ), Integrable f μ → Integrable g μ → ∫ x, (a • f x + b • g x) ∂μ = a • ∫ x, f x ∂μ + b • ∫ x, g x ∂μ) ∧ (∀ (f g : α → ℝ), Integrable f μ → Integrable g μ → f ≤ᵐ[μ] g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ) ∧ (∀ (f g : α → ℝ), f =ᵐ[μ] g → ∫ x, f x ∂μ = ∫ x, g x ∂μ) ∧ (∀ f : α → ℝ, ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ) := by
-- proof
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun f hf => integral_nonneg_of_ae hf
  · intro f g a b hf hg
    have h := integral_add (hf.smul a) (hg.smul b)
    simp only [Pi.smul_apply] at h
    rw [h, integral_smul a f, integral_smul b g]
  · exact fun f g hf hg h => integral_mono_ae hf hg h
  · exact fun f g h => integral_congr_ae h
  · exact fun f => norm_integral_le_integral_norm f


-- created on 2026-10-23
