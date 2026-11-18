import Lemma.Random.Measurable_Wkd.of.All_Measurable_Prob
open MeasureTheory PolicyGradient Random


/--
If every `(x, u) ↦ π_θ(u | x)` is jointly measurable, so is the state value `x ↦ V0 θ γ x`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (h : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.π[θ] z.1 z.2))
  (R : ℝ)
  (θ : Θ)
  (γ : ℝ) :
-- imply
  Measurable (M.V0 R θ γ) := by
-- proof
  change Measurable fun x => ∑' k, γ ^ k * M.Wkd R θ k x
  exact Measurable.tsum fun k =>
    (Measurable_Wkd.of.All_Measurable_Prob (M := M) h R θ k).const_mul (γ ^ k)


-- created on 2026-10-07
-- updated on 2026-11-18