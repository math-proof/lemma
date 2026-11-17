import Def.Analysis.Calculus.Gradient.Operators.Part2
import Mathlib.Analysis.Calculus.ParametricIntegral
import Lemma.Random.GetTSum_SMul.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
import Lemma.Random.Integral_Vkd.eq.TSum_MulPowIntegral_R.of.In_Ico.All_EqWithDensity
import Lemma.Random.HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Real.StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Set Real


/--
`∑' t, γ ^ t • fderiv (∫ r[t]) = ∫ fderiv V0 ∂ init`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [μ : ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.π[θ] z.1 z.2))
  (h₂ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π[θ] sₜ aₜ))
  (h₃ : sup[sₜ] (∫ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) ∂μ.measure) < ∞)
  (hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖))
  (hIntg : ∀ sₜ, Integrable (fun aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖)) μ.measure)
  (θ : Θ) :
-- imply
  ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M.traj θ)) θ =
    ∫ x, fderiv ℝ (fun θ => M.V0 θ γ x) θ ∂(M.init : Measure _) := by
-- proof
  have h₃grad := h₃
  have hGet :=
    GetTSum_SMul.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
      (M := M) h₀ h₁ hπ h₂ h₃ hBdd hIntg θ
  have hobj : (fun θ => ∑' t, γ ^ t * ∫ ω, r t ω ∂(M.traj θ)) =
      fun θ => ∫ x, M.V0 θ γ x ∂(M.init : Measure _) :=
    funext fun θ =>
      (Integral_Vkd.eq.TSum_MulPowIntegral_R.of.In_Ico.All_EqWithDensity
        (M := M) h₀ h₁ hπ θ).symm
  have hV :=
    HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
      (M := M) h₂ h₃grad hBdd hIntg h₀ hπ
  obtain ⟨C, hC⟩ :=
    GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
      (M := M) h₂ h₃grad hBdd hIntg h₀ hπ
  have hCb : ∀ y, ‖fderiv ℝ (fun θ => M.V0 θ γ y) θ‖ ≤ C :=
    fun y => by
      have h := hC ⟨(θ, y), rfl⟩
      simpa [gradient, LinearIsometryEquiv.norm_map] using h
  have hI : HasFDerivAt (fun θ => ∫ x, M.V0 θ γ x ∂(M.init : Measure _))
      (∫ x, fderiv ℝ (fun θ => M.V0 θ γ x) θ ∂(M.init : Measure _)) θ :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun θ x => M.V0 θ γ x)
      (F' := fun θ x => fderiv ℝ (fun θ => M.V0 θ γ x) θ)
      (s := Set.univ) (bound := fun _ => C) Filter.univ_mem
      (Filter.Eventually.of_forall fun θ' =>
        (Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ' γ).aestronglyMeasurable)
      (Integrable.of_bound
        (Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).aestronglyMeasurable
        ((1 - γ)⁻¹ * |M.R|)
        (Filter.Eventually.of_forall fun y =>
          NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ θ y))
      (StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
        (fun θ' => Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ' γ)
        (fun y => (hV y θ).differentiableAt)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y θ' _ => by
        have h := hC ⟨(θ', y), rfl⟩
        simpa [gradient, LinearIsometryEquiv.norm_map] using h)
      (integrable_const _)
      (Filter.Eventually.of_forall fun y θ' _ => (hV y θ').differentiableAt.hasFDerivAt)
  have : fderiv ℝ (fun θ => ∑' t, γ ^ t * ∫ ω, r t ω ∂(M.traj θ)) θ =
      ∫ x, fderiv ℝ (fun θ => M.V0 θ γ x) θ ∂(M.init : Measure _) := by
    rw [hobj, hI.fderiv]
  exact hGet.fderiv.symm.trans this


-- created on 2026-10-20
-- updated on 2026-11-17