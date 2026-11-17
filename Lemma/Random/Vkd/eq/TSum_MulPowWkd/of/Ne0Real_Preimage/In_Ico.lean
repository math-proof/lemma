import Lemma.Random.NormWkd.le.Abs_R
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
`V0` is defined as the discounted `Wkd` series on every state:
`V0 θ γ x = ∑' k, γ ^ k * Wkd θ k x`.
(Hypothesis `_hP` is unused and kept only for path/API compatibility with older callers.)
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
-- given
  (_h : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (sₜ : 𝒮)
  (_hP : (M.traj θ).real ((fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (ω 0).2.1) ⁻¹' {sₜ}) ≠ 0) :
-- imply
  M.V0 θ γ sₜ = ∑' k, γ ^ k * M.Wkd θ k sₜ := rfl


-- created on 2026-10-07
-- updated on 2026-11-16