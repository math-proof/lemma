import Lemma.Random.Measurable_Wkd.of.All_Measurable_Prob
open MeasureTheory PolicyGradient Random


/--
If every `(x, u) ↦ π_θ(u | x)` is jointly measurable, so is the state value `x ↦ V0 θ γ x`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (h : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob θ z.1 z.2))
  (θ : Θ)
  (γ : ℝ) :
-- imply
  Measurable (M.V0 θ γ) := by
-- proof
  have := h
  exact measurable_of_countable _


-- created on 2026-10-07
-- updated on 2026-11-11
