import Lemma.Random.V.eq.Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
import Syntax.Order.Sup
import Instance.Dynamics.PolicyTrajectory
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Filter


/--
On a reachable state, the derivative of the state value equals that of its time-free closed form:
`fderiv ℝ (fun θ' ↦ V θ' γ t x) θ = fderiv ℝ (fun θ' ↦ V0 θ' γ x) θ`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [μ : ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {t : ℕ}
  {sₜ : 𝒮}
  {θ : Θ}
  {R : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.π θ z.1 z.2))
  (h₂ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π θ sₜ aₜ))
  (h₃ : sup[sₜ] (∫ u, sSup (Set.range fun θ => ‖∇[θ] M.π θ sₜ u‖) ∂μ.measure) < ∞)
  (hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖))
  (hIntg : ∀ sₜ, Integrable (fun aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖)) μ.measure)
  (h₄ : (M θ).real (s t ⁻¹' {sₜ}) ≠ 0)
  (hR : ∀ p, (M.reward p : Measure ℝ) (Set.Icc (-R) R) = 1) :
-- imply
  fderiv ℝ (fun θ' => M.V θ' γ t sₜ) θ = fderiv ℝ (fun θ' => M.V0 R θ' γ sₜ) θ := by
-- proof
  exact EventuallyEq.fderiv_eq
    (V.eq.Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
      (M := M) h₀ h₁ hπ h₂ h₃ hBdd hIntg h₄ hR)


-- created on 2026-10-06
-- updated on 2026-11-18