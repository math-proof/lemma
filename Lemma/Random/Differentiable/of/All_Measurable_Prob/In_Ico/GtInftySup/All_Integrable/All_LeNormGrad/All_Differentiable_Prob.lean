import Lemma.Random.HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
open MeasureTheory PolicyGradient Random Set


/--
For a differentiable density policy with a dominated gradient, `θ ↦ V0 θ γ x` is
differentiable on every state. This is the `HasFDerivAt` form
`HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob R`
packaged as differentiability.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
-- given
  (h₀ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π[θ] sₜ aₜ))
  (h₁ : sup[sₜ] (∫ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) ∂ReferenceMeasure.measure) < ∞)
  (hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖))
  (hIntg : ∀ sₜ, Integrable (fun aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖)) ReferenceMeasure.measure)
  (h₄ : γ ∈ Set.Ico 0 1)
  (h₅ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.π[θ] z.1 z.2))
  (R : ℝ)
  (sₜ : 𝒮) :
-- imply
  Differentiable ℝ (fun θ => M.V0 R θ γ sₜ) := by
-- proof
  exact fun θ =>
    (HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
      (M := M) h₀ h₁ hBdd hIntg h₄ h₅ R sₜ θ).differentiableAt


-- created on 2026-11-13
-- updated on 2026-11-18
