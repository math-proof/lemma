import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
Integral against a kernel composition, for a bounded strongly measurable integrand:
`∫ b, f b ∂(κ ∘ₘ μ) = ∫ a, ∫ b, f b ∂(κ a) ∂μ`.
-/
@[path]
private lemma main
  [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} [IsProbabilityMeasure μ]
  {κ : Kernel α β} [IsMarkovKernel κ]
  {f : β → E}
  {C : ℝ}
-- given
  (hf : StronglyMeasurable f)
  (hC : ∀ b, ‖f b‖ ≤ C) :
-- imply
  ∫ b, f b ∂(κ ∘ₘ μ) = ∫ a, ∫ b, f b ∂(κ a) ∂μ := by
-- proof
  rw [← Measure.snd_compProd μ κ, Measure.snd, integral_map measurable_snd.aemeasurable
    hf.aestronglyMeasurable]
  rw [Measure.integral_compProd]
  exact Integrable.of_bound (hf.comp_measurable measurable_snd).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun p => hC p.2)


-- created on 2026-10-07
