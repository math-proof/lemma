import Mathlib.Analysis.InnerProductSpace.Dual
import Lemma.Random.Fderiv.eq.AddIntegral_SMulSMul.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob
import Instance.Dynamics.PolicyTrajectory
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
Policy-gradient recursion for the model value functions on a reachable state x (h₃ : ℙ(s[t] = x) ≠ 0):
∇V(t, x) = ∫ (rkd + γ ∫ V0) • ∇π ∂ref + γ • ∫ π • ∫ ∇V(t+1) ∂T ∂ref.
Gradient (Riesz representative) form of
`Random.Fderiv.eq.AddIntegral_SMulSMul.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
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
  (hγ : γ ∈ Set.Ico 0 1)
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.π θ z.1 z.2))
  (h₁ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π θ sₜ aₜ))
  (h₂ : sup[sₜ] (∫ u, sSup (Set.range fun θ => ‖∇[θ] M.π θ sₜ u‖) ∂ReferenceMeasure.measure) < ∞)
  (hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖))
  (hIntg : ∀ sₜ, Integrable (fun aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖)) ReferenceMeasure.measure)
  (h₃ : (M θ).real (s t ⁻¹' {sₜ}) ≠ 0)
  (hR : ∀ p, (M.reward p : Measure ℝ) (Set.Icc (-R) R) = 1) :
-- imply
  let Q (aₜ : 𝒜) : ℝ :=
    M.rkd R sₜ aₜ + γ * ∫ y, M.V0 R θ γ y ∂(M.trans (sₜ, aₜ));
  ∇[θ] M.V θ γ t sₜ =
    ∫ u, (Q u • ∇[θ] M.π θ sₜ u) ∂ReferenceMeasure.measure +
      γ • ∫ u, (M.π θ sₜ u •
        (∫ y, ∇[θ] M.V θ γ (t + 1) y ∂(M.trans (sₜ, u)))) ∂ReferenceMeasure.measure := by
-- proof
  intro Q
  have hF :=
    Fderiv.eq.AddIntegral_SMulSMul.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob
      (M := M) hγ h₀ hπ h₁ h₂ hBdd hIntg h₃ hR
  have hint₁ :
    (InnerProductSpace.toDual ℝ Θ).symm
      (∫ u, (M.rkd R sₜ u + γ * ∫ y, M.V0 R θ γ y ∂(M.trans (sₜ, u))) •
        fderiv ℝ (fun θ' => M.π θ' sₜ u) θ ∂ReferenceMeasure.measure) =
    ∫ u, (InnerProductSpace.toDual ℝ Θ).symm
      ((M.rkd R sₜ u + γ * ∫ y, M.V0 R θ γ y ∂(M.trans (sₜ, u))) •
        fderiv ℝ (fun θ' => M.π θ' sₜ u) θ) ∂ReferenceMeasure.measure := by
    have h := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv.integral_comp_comm
      (μ := ReferenceMeasure.measure)
      (fun u => (M.rkd R sₜ u + γ * ∫ y, M.V0 R θ γ y ∂(M.trans (sₜ, u))) •
        fderiv ℝ (fun θ' => M.π θ' sₜ u) θ)
    simpa using h.symm
  have hint₂ :
    (InnerProductSpace.toDual ℝ Θ).symm
      (∫ u, (M.π θ sₜ u •
        ∫ y, fderiv ℝ (fun θ' => M.V θ' γ (t + 1) y) θ ∂(M.trans (sₜ, u)))
          ∂ReferenceMeasure.measure) =
    ∫ u, (InnerProductSpace.toDual ℝ Θ).symm
      (M.π θ sₜ u •
        ∫ y, fderiv ℝ (fun θ' => M.V θ' γ (t + 1) y) θ ∂(M.trans (sₜ, u)))
          ∂ReferenceMeasure.measure := by
    have h := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv.integral_comp_comm
      (μ := ReferenceMeasure.measure)
      (fun u => M.π θ sₜ u •
        ∫ y, fderiv ℝ (fun θ' => M.V θ' γ (t + 1) y) θ ∂(M.trans (sₜ, u)))
    simpa using h.symm
  have hint₃ : ∀ u,
    (InnerProductSpace.toDual ℝ Θ).symm
      (∫ y, fderiv ℝ (fun θ' => M.V θ' γ (t + 1) y) θ ∂(M.trans (sₜ, u))) =
    ∫ y, (InnerProductSpace.toDual ℝ Θ).symm
      (fderiv ℝ (fun θ' => M.V θ' γ (t + 1) y) θ) ∂(M.trans (sₜ, u)) := by
    intro u
    have h := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv.integral_comp_comm
      (μ := M.trans (sₜ, u))
      (fun y => fderiv ℝ (fun θ' => M.V θ' γ (t + 1) y) θ)
    simpa using h.symm
  simp only [gradient, Q]
  rw [hF, map_add, map_smul, hint₁, hint₂]
  simp [map_smul, hint₃]


-- created on 2026-11-13
-- updated on 2026-11-18
