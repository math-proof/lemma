import Def.Analysis.Calculus.Gradient.Operators.Part2
import Syntax.Order.Sup
import Lemma.Random.HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.Differentiable_RealPreimageS.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
import Lemma.Random.Integral.eq.MulRealPreimageSIntegral_MulEqS.of.All_EqWithDensity
import Lemma.Random.Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.Wkd.eq.Integral_Kf.of.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Set Real


private lemma cond_r_W
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {t k : ℕ}
  {sₜ : 𝒮}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hP : (M.traj θ).real (s t ⁻¹' {sₜ}) ≠ 0) :
-- imply
  ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {sₜ}] =
    ∫ z, M.Kf θ (fun z => clip z.1 (-M.R) M.R) k z ∂(M.stageK θ sₜ) := by
-- proof
  have hf : StronglyMeasurable (fun z : ℝ × 𝒮 × 𝒜 => clip z.1 (-M.R) M.R) := by
    unfold clip
    exact ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hC : ∀ z : ℝ × 𝒮 × 𝒜, ‖clip z.1 (-M.R) M.R‖ ≤ |M.R| :=
    fun z => NormClip.le.Abs_R _ _
  rw [Integral.eq.MulRealPreimageSIntegral_MulEqS.of.All_EqWithDensity h₀]
  have h₂ :
    ∫ ω, (if s t ω = sₜ then (1:ℝ) else 0) * r (t + k) ω ∂(M.traj θ) =
      ∫ ω, (if s t ω = sₜ then (1:ℝ) else 0) *
        clip (ω (t + k)).1 (-M.R) M.R ∂(M.traj θ) :=
    integral_congr_ae
      ((MEq_Clip.of.All_Eq.All_EqWithDensity h₀ (M := M) θ (t + k)).mono fun ω h => by
        dsimp only
        rw [h])
  rw [h₂, Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    h₀ (M := M) hf hC θ t k sₜ, inv_mul_cancel_left₀ hP]

/--
On a reachable state, `∑' k, γ ^ k • ∇ 𝔼[r[t+k] | s[t] = x] = ∇ V(s[t] = x)`.
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
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.π[θ] z.1 z.2))
  (h₂ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π[θ] sₜ aₜ))
  (h₃ : sup[sₜ] (∫ u, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ u‖) ∂μ.measure) < ∞)
  (hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖))
  (hIntg : ∀ sₜ, Integrable (fun aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖)) μ.measure)
  (h₄ : (M.traj θ).real (s t ⁻¹' {sₜ}) ≠ 0) :
-- imply
  ∑' k, γ ^ k • fderiv ℝ (fun θ => ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {sₜ}]) θ =
    fderiv ℝ (fun θ => M.V θ γ t sₜ) θ := by
-- proof
  obtain ⟨Cg, hCgbound⟩ := id h₃
  have h₅le : ∀ sₜ, ∫ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) ∂μ.measure ≤ Cg := fun x => hCgbound ⟨x, rfl⟩
  have h₃grad := h₃
  have hc : ContinuousAt (fun θ' => (M.traj θ').real (s t ⁻¹' {sₜ})) θ :=
    (Differentiable_RealPreimageS.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
      (M := M) h₁ hπ h₂ h₅le hBdd hIntg t sₜ θ).continuousAt
  have hk : ∀ k, fderiv ℝ (fun θ => ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {sₜ}]) θ =
      fderiv ℝ (fun θ => M.Wkd θ k sₜ) θ := by
    intro k
    have hW : (fun θ => M.Wkd θ k sₜ) =
        fun θ => ∫ z, M.Kf θ (fun z => clip z.1 (-M.R) M.R) k z
          ∂(M.stageK θ sₜ) :=
      funext fun θ => Wkd.eq.Integral_Kf.of.All_EqWithDensity (M := M) θ k sₜ
    refine (Filter.EventuallyEq.fderiv_eq ?_).trans (by rw [hW])
    filter_upwards [hc.eventually_ne h₄] with θ' h
    exact cond_r_W (θ := θ') h₁ h
  simp_rw [hk]
  rw [Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
    (M := M) h₀ h₁ hπ h₂ h₃ hBdd hIntg h₄,
    (HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
      (M := M) h₂ h₃grad hBdd hIntg h₀ hπ sₜ θ).fderiv]


-- created on 2026-10-06
-- updated on 2026-11-17