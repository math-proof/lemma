import Def.Analysis.Calculus.Gradient.Operators.Part2
import Syntax.Order.Sup
import Lemma.Random.HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.Differentiable.All_LeNormFderivMulAdd_1MulAbs_R.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob
open MeasureTheory PolicyGradient PolicyGradient.Model Random Set


/--
The gradients of the closed-form state-value `V0` are bounded over the reachable pairs
`(t, x)`, uniformly in the state, by the discounted series
`∑' k, γ ^ k * (k + 1) * (Cg * |R|)`.
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
  (θ : Θ) :
-- imply
  BddAbove ((fun p : ℕ × 𝒮 => ‖fderiv ℝ (fun θ => M.V0 θ γ p.2) θ‖) ''
    {p | (M.traj θ).real ((fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (ω p.1).2.1) ⁻¹' {p.2}) ≠ 0}) := by
-- proof
  obtain ⟨Cg, hCg⟩ := id h₁
  have hg : ∀ sₜ, ∫ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) ∂ReferenceMeasure.measure ≤ Cg := by
    intro sₜ
    exact hCg ⟨sₜ, rfl⟩
  have hsum : Summable (fun k : ℕ => γ ^ k * ((k + 1) * (Cg * |M.R|))) := by
    have h1 : Summable (fun k : ℕ => (k : ℝ) ^ 1 * γ ^ k) :=
      summable_pow_mul_geometric_of_norm_lt_one 1
        (by simpa [Real.norm_of_nonneg h₄.1] using h₄.2)
    exact ((h1.add (summable_geometric_of_lt_one h₄.1 h₄.2)).mul_right
      (Cg * |M.R|)).congr fun k => by ring
  refine ⟨∑' (k : ℕ), γ ^ k * ((k + 1) * (Cg * |M.R|)), ?_⟩
  rintro _ ⟨p, _, rfl⟩
  beta_reduce
  have hF :=
    HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
      (M := M) h₀ h₁ hBdd hIntg h₄ h₅ p.2 θ
  have hW := fun k =>
    Differentiable.All_LeNormFderivMulAdd_1MulAbs_R.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob
      (M := M) h₅ h₀ hg hBdd hIntg k p.2
  rw [hF.fderiv]
  have hnorm :
    Summable (fun k : ℕ =>
      ‖(γ : ℝ) ^ k • fderiv ℝ (fun θ => M.Wkd θ k p.2) θ‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hsum
    intro k
    rw [norm_smul, norm_pow, Real.norm_of_nonneg h₄.1]
    exact mul_le_mul_of_nonneg_left ((hW k).2 θ) (pow_nonneg h₄.1 k)
  apply (norm_tsum_le_tsum_norm hnorm).trans
  refine hnorm.tsum_le_tsum ?_ hsum
  intro k
  rw [norm_smul, norm_pow, Real.norm_of_nonneg h₄.1]
  exact mul_le_mul_of_nonneg_left ((hW k).2 θ) (pow_nonneg h₄.1 k)


-- created on 2026-11-13
-- updated on 2026-11-16
