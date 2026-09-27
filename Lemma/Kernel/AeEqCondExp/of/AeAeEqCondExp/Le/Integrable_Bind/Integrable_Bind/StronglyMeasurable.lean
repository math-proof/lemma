import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Lemma.Kernel.Integral.eq.Integral_Integral.of.Integrable_Bind
open MeasureTheory ProbabilityTheory Kernel


@[main]
private lemma main
  [MeasurableSpace α] {m m₀ : MeasurableSpace β}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure α} [IsFiniteMeasure μ]
  {κ : Kernel α β} [IsFiniteKernel κ]
  {f g : β → E}
-- given
  (h₀ : StronglyMeasurable[m] g)
  (h₁ : Integrable f (μ.bind κ))
  (h₂ : Integrable g (μ.bind κ))
  (h₃ : m ≤ m₀)
  (h₄ : ∀ᵐ a ∂μ, (κ a)[f | m] =ᵐ[κ a] g) :
-- imply
  (μ.bind κ)[f | m] =ᵐ[μ.bind κ] g := by
-- proof
  refine (ae_eq_condExp_of_forall_setIntegral_eq h₃ h₁ (fun s _ _ => h₂.integrableOn) (fun s hs _ => ?_) h₀.aestronglyMeasurable).symm
  rw [← integral_indicator (h₃ s hs), ← integral_indicator (h₃ s hs), Integral.eq.Integral_Integral.of.Integrable_Bind (h₂.indicator (h₃ s hs)), Integral.eq.Integral_Integral.of.Integrable_Bind (h₁.indicator (h₃ s hs))]
  apply integral_congr_ae
  filter_upwards [h₄, Measure.ae_integrable_of_integrable_comp h₁] with a ha hfa
  rw [integral_indicator (h₃ s hs), integral_indicator (h₃ s hs), ← setIntegral_condExp h₃ hfa hs]
  exact integral_congr_ae (ae_restrict_of_ae ha.symm)


-- created on 2026-09-26