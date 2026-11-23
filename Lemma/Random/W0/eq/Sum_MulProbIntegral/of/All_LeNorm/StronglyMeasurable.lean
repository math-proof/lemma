import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
`∫ z, f z ∂(stageK θ x) = ∫ u, π_θ(u | x) * ∫ ρ, f (ρ, x, u) ∂(reward (x, u)) du`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [μ : ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {f : ℝ × 𝒮 × 𝒜 → ℝ}
  {C : ℝ}
-- given
  (h₀ : StronglyMeasurable f)
  (h₁ : ∀ z, ‖f z‖ ≤ C)
  (θ : Θ)
  (sₜ : 𝒮) :
-- imply
  ∫ z, f z ∂(M.stageK θ sₜ) =
    ∫ (aₜ : 𝒜), (M.π θ sₜ aₜ * ∫ ρ, f (ρ, sₜ, aₜ) ∂(M.reward (sₜ, aₜ)))
      ∂μ.measure := by
-- proof
  rw [Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity (M := M) h₀ h₁ θ]
  simp [smul_eq_mul]


-- created on 2026-10-07
-- updated on 2026-11-17