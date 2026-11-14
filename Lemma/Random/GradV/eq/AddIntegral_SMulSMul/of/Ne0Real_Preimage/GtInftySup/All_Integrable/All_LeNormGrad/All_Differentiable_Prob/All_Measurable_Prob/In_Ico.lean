import Mathlib.Analysis.InnerProductSpace.Dual
import Lemma.Random.Fderiv.eq.AddIntegral_SMulSMul.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random


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
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {g : 𝒮 → 𝒜 → ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {t : ℕ}
  {x : 𝒮}
  {θ : Θ}
-- given
  (hγ : γ ∈ Set.Ico 0 1)
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob θ z.1 z.2))
  (h₁ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₂ : ∀ θ x u, ‖∇[θ] M.policy.prob θ x u‖ ≤ g x u)
  (hg : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (hsup : sup[x] ∫ u, g x u ∂ReferenceMeasure.measure < ∞)
  (h₃ : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  let Q (u : 𝒜) : ℝ :=
    M.rkd x u + γ * ∫ y, M.V0 θ γ y ∂(M.env.trans (x, u));
  ∇[θ] M.V θ γ t x =
    ∫ u, (Q u • ∇[θ] M.policy.prob θ x u) ∂ReferenceMeasure.measure +
      γ • ∫ u, (M.policy.prob θ x u •
        (∫ y, ∇[θ] M.V θ γ (t + 1) y ∂(M.env.trans (x, u)))) ∂ReferenceMeasure.measure := by
-- proof
  intro Q
  have hF :=
    Fderiv.eq.AddIntegral_SMulSMul.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob
      (M := M) hγ h₀ hπ h₁ h₂ hg hsup h₃
  have hint₁ :
    (InnerProductSpace.toDual ℝ Θ).symm
      (∫ u, (M.rkd x u + γ * ∫ y, M.V0 θ γ y ∂(M.env.trans (x, u))) •
        fderiv ℝ (fun θ' => M.policy.prob θ' x u) θ ∂ReferenceMeasure.measure) =
    ∫ u, (InnerProductSpace.toDual ℝ Θ).symm
      ((M.rkd x u + γ * ∫ y, M.V0 θ γ y ∂(M.env.trans (x, u))) •
        fderiv ℝ (fun θ' => M.policy.prob θ' x u) θ) ∂ReferenceMeasure.measure := by
    have h := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv.integral_comp_comm
      (μ := (ReferenceMeasure.measure : Measure 𝒜))
      (fun u => (M.rkd x u + γ * ∫ y, M.V0 θ γ y ∂(M.env.trans (x, u))) •
        fderiv ℝ (fun θ' => M.policy.prob θ' x u) θ)
    simpa using h.symm
  have hint₂ :
    (InnerProductSpace.toDual ℝ Θ).symm
      (∫ u, (M.policy.prob θ x u •
        ∫ y, fderiv ℝ (fun θ' => M.V θ' γ (t + 1) y) θ ∂(M.env.trans (x, u)))
          ∂ReferenceMeasure.measure) =
    ∫ u, (InnerProductSpace.toDual ℝ Θ).symm
      (M.policy.prob θ x u •
        ∫ y, fderiv ℝ (fun θ' => M.V θ' γ (t + 1) y) θ ∂(M.env.trans (x, u)))
          ∂ReferenceMeasure.measure := by
    have h := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv.integral_comp_comm
      (μ := (ReferenceMeasure.measure : Measure 𝒜))
      (fun u => M.policy.prob θ x u •
        ∫ y, fderiv ℝ (fun θ' => M.V θ' γ (t + 1) y) θ ∂(M.env.trans (x, u)))
    simpa using h.symm
  have hint₃ : ∀ u,
    (InnerProductSpace.toDual ℝ Θ).symm
      (∫ y, fderiv ℝ (fun θ' => M.V θ' γ (t + 1) y) θ ∂(M.env.trans (x, u))) =
    ∫ y, (InnerProductSpace.toDual ℝ Θ).symm
      (fderiv ℝ (fun θ' => M.V θ' γ (t + 1) y) θ) ∂(M.env.trans (x, u)) := by
    intro u
    have h := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv.integral_comp_comm
      (μ := M.env.trans (x, u))
      (fun y => fderiv ℝ (fun θ' => M.V θ' γ (t + 1) y) θ)
    simpa using h.symm
  simp only [gradient, Q]
  rw [hF, map_add, map_smul, hint₁, hint₂]
  simp [map_smul, hint₃]


-- created on 2026-11-13
