import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Theorem.Function
import Lemma.Random.GetTSum_SMul.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
import Lemma.Random.ExpectDotPow_Id.eq.Integral_ExtDotPow_Id.of.All_EqWithDensity
import Lemma.Random.TSum_SMul.eq.Integral_Fderiv_Vkd.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
import Lemma.Random.Integral_Fderiv_Vkd.eq.TSum_SMul_Integral_SMul_Qkd_FderivLog.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Integral_SMul_Qkd.eq.Integral_SMul_SubAddVkd.of.In_Ico.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Integral_SMul.of.In_Ico.In_Ico.All_EqWithDensity
import Lemma.Random.Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.AeAll_LeNorm_TSum_MulPowSubAddRMul_VkdVkdMulSub1DeltaBound.of.In_Ico.In_Ico.All_EqWithDensity
import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.PSpace_Path.of.All_PSpace
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.SubAddKfMul_KfKf.eq.Zero.of.In_Ico.All_EqWithDensity
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Random.NormClip.le.Abs_R
import Lemma.Random.AeNormSub.le.DeltaBound.of.In_Ico.All_EqWithDensity
import Lemma.Random.Integral_SMul.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Filter Topology Random Measure Real
set_option maxHeartbeats 900000


private lemma int_hist_mul
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  (M : DensityModel Θ 𝒮 𝒜) (θ : Θ) (n k : ℕ)
  {G : ((Finset.Iic n) → ℝ × 𝒮 × 𝒜) → ℝ}
  (hG : StronglyMeasurable G) {CG : ℝ} (hCG : ∀ h, ‖G h‖ ≤ CG)
  {g : (ℝ × 𝒮 × 𝒜) → ℝ} (hg : StronglyMeasurable g) {C : ℝ} (hC : ∀ z, ‖g z‖ ≤ C) :
  Integrable (fun ω => G (Preorder.frestrictLe n ω) * g (ω k)) (M θ) := by
  refine Integrable.of_bound (C := CG * C) ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact ((hG.comp_measurable (Preorder.measurable_frestrictLe n)).mul
      (hg.comp_measurable (measurable_pi_apply k))).aestronglyMeasurable
  ·
    rw [norm_mul]
    exact mul_le_mul (hCG _) (hC _) (norm_nonneg _)
      ((norm_nonneg _).trans (hCG (Preorder.frestrictLe n ω)))


/--
For `t ≤ n`, `𝔼[δ[n+1] * ψ(s[t], a[t])] = 0` under the continuous-action path law
(Markov property along histories + Bellman equation).
-/
private lemma zero_V0
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (t n : ℕ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 ↦ M.policy.prob θ z.1 z.2))
  (h₂ : t ≤ n)
  (θ : Θ)
  (ψ : 𝒮 → 𝒜 → ℝ)
  (hψ : StronglyMeasurable (Function.uncurry ψ))
  (hMs : ∃ Ms : ℝ, ∀ y u, ‖ψ y u‖ ≤ Ms) :
-- imply
  ∫ ω, (r (n + 1) ω + γ * M.V0 θ γ (s (n + 1 + 1) ω) - M.V0 θ γ (s (n + 1) ω)) *
    ψ (s t ω) (a t ω) ∂(M θ) = 0 := by
-- proof
  classical
  obtain ⟨Ms, hMsle⟩ := hMs
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω ↦ (ω t).2.2
  let Gh : ((Finset.Iic n) → ℝ × 𝒮 × 𝒜) → ℝ := fun h =>
    ψ (h ⟨t, Finset.mem_Iic.2 h₂⟩).2.1 (h ⟨t, Finset.mem_Iic.2 h₂⟩).2.2
  have hG : StronglyMeasurable Gh :=
    hψ.comp_measurable
      ((measurable_snd.fst.comp (measurable_pi_apply _)).prodMk
        (measurable_snd.snd.comp (measurable_pi_apply _)))
  have hCG : ∀ h, ‖Gh h‖ ≤ Ms := fun h => hMsle _ _
  let fV : (ℝ × 𝒮 × 𝒜) → ℝ := fun w => M.V0 θ γ w.2.1
  have hfV : StronglyMeasurable fV :=
    ((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp measurable_snd.fst).stronglyMeasurable
  have hCV : ∀ w, ‖fV w‖ ≤ (1 - γ)⁻¹ * |M.env.R| :=
    fun w => NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ θ w.2.1
  have hclip : StronglyMeasurable fun (w : ℝ × 𝒮 × 𝒜) => clip w.1 (-M.env.R) M.env.R :=
    ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hCclip : ∀ (w : ℝ × 𝒮 × 𝒜), ‖clip w.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
    fun w => NormClip.le.Abs_R M.env.R w.1
  have h1 := All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hclip hCclip θ 1 n hG hCG
  have h2 := All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hfV hCV θ 2 n hG hCG
  have h3 := All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hfV hCV θ 1 n hG hCG
  have i1 := int_hist_mul M θ n (n + 1) hG hCG hclip hCclip
  have i2 := int_hist_mul M θ n (n + 2) hG hCG hfV hCV
  have i3 := int_hist_mul M θ n (n + 1) hG hCG hfV hCV
  have k1 := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hclip hCclip θ 1
  have k2 := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hfV hCV θ 2
  have k3 := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hfV hCV θ 1
  have j1 := int_hist_mul M θ n n hG hCG k1.1 k1.2
  have j2 := int_hist_mul M θ n n hG hCG k2.1 k2.2
  have j3 := int_hist_mul M θ n n hG hCG k3.1 k3.2
  have hae : ∀ᵐ ω ∂(M θ),
      (r (n + 1) ω + γ * M.V0 θ γ (s (n + 1 + 1) ω) - M.V0 θ γ (s (n + 1) ω)) *
        ψ (s t ω) (a t ω) =
        Gh (Preorder.frestrictLe n ω) * clip (ω (n + 1)).1 (-M.env.R) M.env.R +
          γ * (Gh (Preorder.frestrictLe n ω) * fV (ω (n + 2))) -
          Gh (Preorder.frestrictLe n ω) * fV (ω (n + 1)) := by
    filter_upwards [MEq_Clip.of.All_Eq.All_EqWithDensity h₁ (M := M) θ (n + 1)] with ω hω
    have hGω : Gh (Preorder.frestrictLe n ω) = ψ (s t ω) (a t ω) := rfl
    rw [hGω, hω, mul_comm (ψ (s t ω) (a t ω))]
    ring
  have hz : ∀ ω : ℕ → ℝ × 𝒮 × 𝒜,
      Gh (Preorder.frestrictLe n ω) *
          M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 1 (ω n) +
        γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ fV 2 (ω n)) -
        Gh (Preorder.frestrictLe n ω) * M.Kf θ fV 1 (ω n) = 0 := fun ω => by
    have := SubAddKfMul_KfKf.eq.Zero.of.In_Ico.All_EqWithDensity (M := M) h₀ hπ θ (ω n)
    calc
      _ = Gh (Preorder.frestrictLe n ω) *
          (M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 1 (ω n) +
            γ * M.Kf θ fV 2 (ω n) - M.Kf θ fV 1 (ω n)) := by
        ring
      _ = 0 := by rw [this, mul_zero]
  have i23 : Integrable (fun ω => γ * (Gh (Preorder.frestrictLe n ω) * fV (ω (n + 2)))) (M θ) :=
    i2.const_mul γ
  have j23 : Integrable (fun ω => γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ fV 2 (ω n))) (M θ) :=
    j2.const_mul γ
  have ia : Integrable (fun ω => Gh (Preorder.frestrictLe n ω) *
      clip (ω (n + 1)).1 (-M.env.R) M.env.R +
        γ * (Gh (Preorder.frestrictLe n ω) * fV (ω (n + 2)))) (M θ) := i1.add i23
  have ja : Integrable (fun ω => Gh (Preorder.frestrictLe n ω) *
      M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 1 (ω n) +
        γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ fV 2 (ω n))) (M θ) := j1.add j23
  rw [integral_congr_ae hae, integral_sub ia i3, integral_add i1 i23, integral_const_mul,
    h1, h2, h3]
  have e := integral_sub ja j3
  rw [integral_add j1 j23, integral_const_mul] at e
  rw [← e]
  simp_rw [hz]
  simp

private lemma integral_delta_smul_eq_zero
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜} {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  (t n : ℕ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 ↦ M.policy.prob θ z.1 z.2))
  (h₂ : t ≤ n)
  (θ : Θ)
  (ψ : 𝒮 → 𝒜 → Θ →L[ℝ] ℝ)
  (hψ : StronglyMeasurable (Function.uncurry ψ))
  (hMs : ∃ Ms : ℝ, ∀ y u, ‖ψ y u‖ ≤ Ms) :
  ∫ ω, (r (n + 1) ω + γ * M.V0 θ γ (s (n + 1 + 1) ω) - M.V0 θ γ (s (n + 1) ω)) •
    ψ (s t ω) (a t ω) ∂(M θ) = 0 := by
  obtain ⟨Ms, hMsle⟩ := hMs
  refine ContinuousLinearMap.ext fun v => ?_
  have hφ : StronglyMeasurable (Function.uncurry fun y u => (ψ y u) v) :=
    (continuous_eval_const v).comp_stronglyMeasurable hψ
  have hφb : ∃ Ms' : ℝ, ∀ y u, ‖(ψ y u) v‖ ≤ Ms' :=
    ⟨Ms * ‖v‖, fun y u =>
      (ContinuousLinearMap.le_opNorm (ψ y u) v).trans
        (mul_le_mul_of_nonneg_right (hMsle y u) (norm_nonneg v))⟩
  set Bδ : ℝ := (3 / (1 - γ) - 1) * |M.env.R|
  have hInt :
      Integrable (fun ω =>
        (r (n + 1) ω + γ * M.V0 θ γ (s (n + 1 + 1) ω) - M.V0 θ γ (s (n + 1) ω)) •
          ψ (s t ω) (a t ω)) (M θ) := by
    refine Integrable.of_bound
      ((((Random.Measurable.of.All_Eq.fst h₁ (n + 1)).add
          (((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp
            (Random.Measurable.of.All_Eq.snd.fst h₁ (n + 1 + 1))).const_mul γ)).sub
        ((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp
          (Random.Measurable.of.All_Eq.snd.fst h₁ (n + 1)))).stronglyMeasurable.smul
        (hψ.comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
            (Random.Measurable.of.All_Eq.snd.snd h₁ t)))).aestronglyMeasurable
      (Bδ * Ms) ?_
    filter_upwards [AeNormSub.le.DeltaBound.of.In_Ico.All_EqWithDensity (M := M) h₀ h₁ θ] with ω hδ
    rw [norm_smul]
    have hB0 : 0 ≤ Bδ := by
      refine mul_nonneg ?_ (abs_nonneg _)
      refine sub_nonneg.2 ?_
      have hγ : 0 < 1 - γ := sub_pos.2 h₀.2
      exact (one_le_div₀ hγ).2 (by linarith [h₀.1, h₀.2])
    exact mul_le_mul (hδ _) (hMsle _ _) (norm_nonneg _) hB0
  rw [ContinuousLinearMap.integral_apply hInt v]
  simp_rw [_root_.smul_apply, smul_eq_mul]
  exact zero_V0
    (M := M) t n h₀ h₁ hπ h₂ θ (fun y u => (ψ y u) v) hφ hφb


/--
GAE reduction under the continuous-action path law:
`∫ ((∑' k, c ^ k * δ[t + k]) • ψ(s[t], a[t])) = ∫ (δ[t] • ψ(s[t], a[t]))`.
-/
private lemma collapse_V0
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ c : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 ↦ M.policy.prob θ z.1 z.2))
  (θ : Θ)
  (h₂ : c ∈ Set.Ico 0 1)
  (t : ℕ)
  (ψ : 𝒮 → 𝒜 → Θ →L[ℝ] ℝ)
  (hψ : StronglyMeasurable (Function.uncurry ψ))
  (hMs : ∃ Ms : ℝ, ∀ y u, ‖ψ y u‖ ≤ Ms) :
-- imply
  ∫ ω, (∑' k, c ^ k * (r (t + k) ω + γ * M.V0 θ γ (s (t + k + 1) ω) -
    M.V0 θ γ (s (t + k) ω))) • ψ (s t ω) (a t ω) ∂(M θ) =
    ∫ ω, (r t ω + γ * M.V0 θ γ (s (t + 1) ω) - M.V0 θ γ (s t ω)) •
      ψ (s t ω) (a t ω) ∂(M θ) := by
-- proof
  classical
  obtain ⟨Ms, hMsle⟩ := hMs
  let F : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → (Θ →L[ℝ] ℝ) := fun k ω =>
    (c ^ k * (r (t + k) ω + γ * M.V0 θ γ (s (t + k + 1) ω) - M.V0 θ γ (s (t + k) ω))) •
      ψ (s t ω) (a t ω)
  have hF : ∀ k ω, F k ω = c ^ k • ((r (t + k) ω + γ * M.V0 θ γ (s (t + k + 1) ω) -
      M.V0 θ γ (s (t + k) ω)) • ψ (s t ω) (a t ω)) := fun k ω => by
    simp only [F, mul_smul]
  set Bδ : ℝ := (3 / (1 - γ) - 1) * |M.env.R|
  have hB0 : 0 ≤ Bδ := by
    refine mul_nonneg ?_ (abs_nonneg _)
    refine sub_nonneg.2 ?_
    have hγ : 0 < 1 - γ := sub_pos.2 h₀.2
    exact (one_le_div₀ hγ).2 (by linarith [h₀.1, h₀.2])
  have hδm : ∀ k, Measurable fun ω =>
      r (t + k) ω + γ * M.V0 θ γ (s (t + k + 1) ω) - M.V0 θ γ (s (t + k) ω) := fun k =>
    ((Random.Measurable.of.All_Eq.fst h₁ (t + k)).add
      (((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp
        (Random.Measurable.of.All_Eq.snd.fst h₁ (t + k + 1))).const_mul γ)).sub
      ((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp
        (Random.Measurable.of.All_Eq.snd.fst h₁ (t + k)))
  have hFi : ∀ k, Integrable (F k) (M θ) := fun k => by
    refine Integrable.of_bound
      (((hδm k).const_mul (c ^ k)).stronglyMeasurable.smul
        (hψ.comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
            (Random.Measurable.of.All_Eq.snd.snd h₁ t)))).aestronglyMeasurable
      (c ^ k * (Bδ * Ms)) ?_
    filter_upwards [AeNormSub.le.DeltaBound.of.In_Ico.All_EqWithDensity (M := M) h₀ h₁ θ] with ω h
    rw [hF, norm_smul, norm_smul, norm_pow, Real.norm_of_nonneg h₂.1]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₂.1 k)
    exact mul_le_mul (h _) (hMsle _ _) (norm_nonneg _) hB0
  have hFb : ∀ k, ∀ᵐ ω ∂(M θ), ‖F k ω‖ ≤ c ^ k * (Bδ * Ms) := fun k => by
    filter_upwards [AeNormSub.le.DeltaBound.of.In_Ico.All_EqWithDensity (M := M) h₀ h₁ θ] with ω h
    rw [hF, norm_smul, norm_smul, norm_pow, Real.norm_of_nonneg h₂.1]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₂.1 k)
    exact mul_le_mul (h _) (hMsle _ _) (norm_nonneg _) hB0
  have hsum : Summable (fun k => ∫ ω, ‖F k ω‖ ∂(M θ)) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one h₂.1 h₂.2).mul_right (Bδ * Ms))
    calc
      _ ≤ ∫ _, c ^ k * (Bδ * Ms) ∂(M θ) :=
        integral_mono_ae (hFi k).norm (integrable_const _) (hFb k)
      _ = c ^ k * (Bδ * Ms) := by simp
  have hHas := hasSum_integral_of_summable_integral_norm hFi hsum
  have hzero : ∀ k, (k ≠ 0) → (∫ ω, F k ω ∂(M θ) = 0) := by
    intro k hk
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    simp_rw [hF]
    rw [integral_smul]
    have := integral_delta_smul_eq_zero (M := M) t (t + k') h₀ h₁ hπ (Nat.le_add_right t k') θ ψ hψ ⟨Ms, hMsle⟩
    rw [show (fun ω => (r (t + k'.succ) ω + γ * M.V0 θ γ (s (t + k'.succ + 1) ω) -
        M.V0 θ γ (s (t + k'.succ) ω)) • ψ (s t ω) (a t ω)) = fun ω => (r (t + k' + 1) ω +
        γ * M.V0 θ γ (s (t + k' + 1 + 1) ω) - M.V0 θ γ (s (t + k' + 1) ω)) • ψ (s t ω) (a t ω)
        from rfl, this, smul_zero]
  have h0 : ∑' k, ∫ ω, F k ω ∂(M θ) = ∫ ω, F 0 ω ∂(M θ) := tsum_eq_single 0 hzero
  have hae : ∀ᵐ ω ∂(M θ), (∑' k, c ^ k * (r (t + k) ω + γ * M.V0 θ γ (s (t + k + 1) ω) -
        M.V0 θ γ (s (t + k) ω))) • ψ (s t ω) (a t ω) = ∑' k, F k ω := by
    filter_upwards [AeNormSub.le.DeltaBound.of.In_Ico.All_EqWithDensity (M := M) h₀ h₁ θ] with ω h
    have hs : Summable (fun k => c ^ k * (r (t + k) ω + γ * M.V0 θ γ (s (t + k + 1) ω) -
        M.V0 θ γ (s (t + k) ω))) := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h₂.1 h₂.2).mul_right Bδ)
        fun k => ?_
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₂.1]
      exact mul_le_mul_of_nonneg_left (h _) (pow_nonneg h₂.1 k)
    exact (hs.tsum_smul_const _).symm
  rw [integral_congr_ae hae, ← hHas.tsum_eq, h0]
  simp [F]


private lemma ae_norm_residual
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜} {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ) :
  ∀ᵐ ω ∂(M θ), ∀ j,
    ‖r j ω + γ * M.V θ γ (j + 1) (s (j + 1) ω) - M.V θ γ j (s j ω)‖ ≤
      (2 / (1 - γ)) * |M.env.R| := by
  obtain rfl : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω ↦ (ω t).2.2
  set BV : ℝ := (1 - γ)⁻¹ * |M.env.R|
  have hBV0 : 0 ≤ BV :=
    mul_nonneg (inv_nonneg.2 (le_of_lt (sub_pos.2 h₀.2))) (abs_nonneg _)
  have hrm : ∀ k, Measurable (r k) := fun k => Random.Measurable.of.All_Eq.fst h₁ k
  have hsm : ∀ k, Measurable (s k) := fun k => Random.Measurable.of.All_Eq.snd.fst h₁ k
  have hpR : Measurable (fun ω i => r i ω) := Measurable.of_eval hrm
  have hfGret : ∀ k, Measurable
      (fun integ : ℕ → ℝ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) := fun k =>
    Measurable.tsum fun j => (measurable_pi_apply (k + j)).const_mul _
  have hr_bd : ∀ᵐ ω ∂(M θ), ∀ j, |r j ω| ≤ |M.env.R| := by
    have hcl : ∀ j,
        r j =ᵐ[M θ] fun ω => clip (ω j).1 (-M.env.R) M.env.R := fun j =>
      MEq_Clip.of.All_Eq.All_EqWithDensity h₁ (M := M) θ j
    have hcl' : ∀ᵐ ω ∂(M θ), ∀ j,
        r j ω = clip (ω j).1 (-M.env.R) M.env.R :=
      (ae_all_iff (ι := ℕ)).mpr hcl
    filter_upwards [hcl'] with ω hω j
    rw [hω j, ← Real.norm_eq_abs]
    exact NormClip.le.Abs_R (R := M.env.R) (ρ := (ω j).1)
  have hret_bd : ∀ᵐ ω ∂(M θ), ∀ k,
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:])‖ ≤ BV := by
    have hgeo := (hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|
    filter_upwards [hr_bd] with ω hω k
    refine tsum_of_norm_bounded hgeo fun j => ?_
    have hid : (γ ^ (id : ℕ → ℕ)) j = γ ^ j := rfl
    have hslice : (fun i => r i ω)[k:] j = r (k + j) ω := rfl
    rw [hid, hslice, norm_mul, norm_pow, Real.norm_of_nonneg h₀.1, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hω (k + j)) (pow_nonneg h₀.1 j)
  have hret : ∀ k, Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
      (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:] := fun k =>
    (hfGret k).comp hpR
  have hGi : ∀ k,
      Integrable (fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:]) (M θ) :=
    fun k =>
      Integrable.of_bound (hret k).aestronglyMeasurable BV
        (by filter_upwards [hret_bd] with ω hω; exact hω k)
  have hV_ae : ∀ k,
      (fun ω => M.V θ γ k (s k ω)) =ᵐ[M θ]
        Expectation.condSigma (M θ) (fun ω i => r i ω) (s k)
          (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) := fun k => by
    have hcomp :=
      Expectation.condEval_comp_ae_eq_condSigma
        (x := fun ω i => r i ω) (y := s k)
        (f := fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:])
        hpR.aemeasurable (hsm k) (hfGret k).stronglyMeasurable (hGi k)
    filter_upwards [hcomp] with ω hω
    exact hω
  have hVbd : ∀ᵐ ω ∂(M θ), ∀ k, |M.V θ γ k (s k ω)| ≤ BV := by
    have hcond : ∀ k, ∀ᵐ ω ∂(M θ),
        |Expectation.condSigma (M θ) (fun ω i => r i ω) (s k)
          (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) ω| ≤ BV := fun k => by
      have hbd :=
        ae_bdd_norm_condExp_of_ae_bdd_norm
          (f := fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun i => r i ω)[k:])
          (m := MeasurableSpace.comap (s k) inferInstance)
          (by filter_upwards [hret_bd] with ω hω; exact hω k)
      filter_upwards [hbd] with ω h
      simpa [Expectation.condSigma, Real.norm_eq_abs] using h
    have hVeq := (ae_all_iff (ι := ℕ)).mpr hV_ae
    have hVnorm := (ae_all_iff (ι := ℕ)).mpr hcond
    filter_upwards [hVeq, hVnorm] with ω heq hnorm k
    rw [heq k]
    exact hnorm k
  have hB : (2 / (1 - γ)) * |M.env.R| = |M.env.R| + (1 + γ) * BV := by
    have hpos : 1 - γ ≠ 0 := (sub_pos.2 h₀.2).ne'
    simp [BV, div_eq_mul_inv, add_mul, mul_assoc]
    field_simp [hpos]
    ring
  filter_upwards [hr_bd, hVbd] with ω hr hv j
  rw [Real.norm_eq_abs]
  have hsum : |r j ω + γ * M.V θ γ (j + 1) (s (j + 1) ω) - M.V θ γ j (s j ω)| ≤
      |r j ω| + |γ * M.V θ γ (j + 1) (s (j + 1) ω)| + |M.V θ γ j (s j ω)| := by
    have h1 := abs_add_le (r j ω) (γ * M.V θ γ (j + 1) (s (j + 1) ω))
    have h2 : |r j ω + γ * M.V θ γ (j + 1) (s (j + 1) ω) - M.V θ γ j (s j ω)| ≤
        |r j ω + γ * M.V θ γ (j + 1) (s (j + 1) ω)| + |M.V θ γ j (s j ω)| := by
      simpa [sub_eq_add_neg, abs_neg] using
        abs_add_le (r j ω + γ * M.V θ γ (j + 1) (s (j + 1) ω)) (-M.V θ γ j (s j ω))
    exact h2.trans (add_le_add h1 le_rfl)
  have : |r j ω| + |γ * M.V θ γ (j + 1) (s (j + 1) ω)| + |M.V θ γ j (s j ω)| ≤
      |M.env.R| + (1 + γ) * BV := by
    have hγV : |γ * M.V θ γ (j + 1) (s (j + 1) ω)| ≤ γ * BV := by
      rw [abs_mul, abs_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (hv (j + 1)) h₀.1
    have := add_le_add (add_le_add (hr j) hγV) (hv j)
    have hrew : γ * BV + BV = (1 + γ) * BV := by ring
    simpa [hrew, add_assoc] using this
  exact hsum.trans (this.trans_eq hB.symm)


private lemma sum_range_residual_tele
  (W : ℕ → 𝒮 → ℝ) (γ : ℝ)
  (r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ)
  (s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮)
  (t N : ℕ) (ω : ℕ → ℝ × 𝒮 × 𝒜) :
  ∑ k ∈ Finset.range N,
      γ ^ k * (r (t + k) ω + γ * W (t + k + 1) (s (t + k + 1) ω) -
        W (t + k) (s (t + k) ω)) =
    ∑ k ∈ Finset.range N, γ ^ k * r (t + k) ω +
      γ ^ N * W (t + N) (s (t + N) ω) - W t (s t ω) := by
  induction N with
  | zero =>
    simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have hN : t + N + 1 = t + (N + 1) := by omega
    simp only [hN]
    ring


private lemma tsum_residual_eq_return_sub
  (W : ℕ → 𝒮 → ℝ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1)
  (r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ)
  (s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮)
  (t : ℕ) (ω : ℕ → ℝ × 𝒮 × 𝒜)
  {R BV : ℝ} (_hR0 : 0 ≤ R) (_hBV : 0 ≤ BV)
  (hr : ∀ n, |r n ω| ≤ R)
  (hW : ∀ n, |W n (s n ω)| ≤ BV) :
  ∑' k, γ ^ k * (r (t + k) ω + γ * W (t + k + 1) (s (t + k + 1) ω) -
      W (t + k) (s (t + k) ω)) =
    (∑' k, γ ^ k * r (t + k) ω) - W t (s t ω) := by
  set δ : ℕ → ℝ := fun k =>
    r (t + k) ω + γ * W (t + k + 1) (s (t + k + 1) ω) - W (t + k) (s (t + k) ω)
  have hsumr : Summable fun k : ℕ => γ ^ k * r (t + k) ω := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hγ.1 hγ.2).mul_right R) ?_
    intro k
    rw [norm_mul, norm_pow, Real.norm_of_nonneg hγ.1, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hr (t + k)) (pow_nonneg hγ.1 k)
  have hsumδ : Summable fun k : ℕ => γ ^ k * δ k := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hγ.1 hγ.2).mul_right (R + (1 + γ) * BV)) ?_
    intro k
    rw [norm_mul, norm_pow, Real.norm_of_nonneg hγ.1, Real.norm_eq_abs]
    have h1 := abs_add_le (r (t + k) ω) (γ * W (t + k + 1) (s (t + k + 1) ω))
    have h2 : |δ k| ≤
        |r (t + k) ω + γ * W (t + k + 1) (s (t + k + 1) ω)| +
          |W (t + k) (s (t + k) ω)| := by
      simpa [δ, sub_eq_add_neg, abs_neg] using
        abs_add_le (r (t + k) ω + γ * W (t + k + 1) (s (t + k + 1) ω))
          (-W (t + k) (s (t + k) ω))
    have hγW : |γ * W (t + k + 1) (s (t + k + 1) ω)| ≤ γ * BV := by
      rw [abs_mul, abs_of_nonneg hγ.1]
      exact mul_le_mul_of_nonneg_left (hW (t + k + 1)) hγ.1
    have hδbd : |δ k| ≤ R + (1 + γ) * BV := by
      have := h2.trans (add_le_add h1 le_rfl)
      have := this.trans (add_le_add (add_le_add (hr (t + k)) hγW) (hW (t + k)))
      have hrew : R + γ * BV + BV = R + (1 + γ) * BV := by ring
      simpa [add_assoc, hrew] using this
    exact mul_le_mul_of_nonneg_left hδbd (pow_nonneg hγ.1 k)
  have hpartial : ∀ N,
      ∑ k ∈ Finset.range N, γ ^ k * δ k =
        ∑ k ∈ Finset.range N, γ ^ k * r (t + k) ω +
          γ ^ N * W (t + N) (s (t + N) ω) - W t (s t ω) :=
    fun N => sum_range_residual_tele W γ r s t N ω
  have hlimW : Tendsto (fun N : ℕ => γ ^ N * W (t + N) (s (t + N) ω)) atTop (nhds 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hγ.1 hγ.2
    have hpowBV : Tendsto (fun N : ℕ => γ ^ N * BV) atTop (nhds 0) := by
      simpa [zero_mul] using hpow.mul_const BV
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    refine squeeze_zero (fun _ => norm_nonneg _) ?_ hpowBV
    intro N
    rw [norm_mul, norm_pow, Real.norm_of_nonneg hγ.1, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hW (t + N)) (pow_nonneg hγ.1 N)
  have hps : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, γ ^ k * δ k) atTop
      (nhds ((∑' k, γ ^ k * r (t + k) ω) - W t (s t ω))) := by
    simp_rw [hpartial]
    simpa [add_zero] using
      (hsumr.hasSum.tendsto_sum_nat.add hlimW).sub
        (tendsto_const_nhds (x := W t (s t ω)))
  exact tendsto_nhds_unique hsumδ.hasSum.tendsto_sum_nat hps


/--
Unbiased continuous-action advantage estimate: with textbook
`M.V θ γ t : 𝒮 → ℝ` and density score `∇ log π`,
`∇𝔼[(γ ^ id) ⬝ᵥ r] = 𝔼[(γ ^ id) ⬝ᵥ fun t ↦ ((γ ^ id) ⬝ᵥ (r[t:] + γ • (fun j => M.V θ γ (t+1+j) (s[t+1:] j)) - fun j => M.V θ γ (t+j) (s[t:] j))) • ∇ log π]`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [μ : ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {γ : ℝ}
  {g : 𝒮 → 𝒜 → ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob θ z.1 z.2))
  (hVm : ∀ k, Measurable (M.V θ γ k))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ g x u)
  (h₄ : ∀ x, Integrable (g x) μ.measure)
  (h₅ : sup[x] ∫ u, g x u ∂μ.measure < ∞)
  (hφ : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ))
  (hMs : sup[y, u] ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ < ∞) :
-- imply
  have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V_δ : ℕ ⇀ (ℕ → 𝒮) → ℕ → ℝ := ⟨fun t δ k => M.V θ γ (t + k) (δ k)⟩
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      (((γ ^ (id : ℕ → ℕ)) ⬝ᵥ (r[t:] + γ • V_δ[t + 1] s[t + 1:] - V_δ[t] s[t:])) •
        ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) := by
-- proof
  obtain ⟨Cg, hCg⟩ := id h₅
  have h₅le : ∀ x, ∫ u, g x u ∂μ.measure ≤ Cg := fun x => hCg ⟨x, rfl⟩
  obtain ⟨Ms, hMsb⟩ := id hMs
  have hMsle : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms :=
    fun y u => hMsb ⟨(y, u), rfl⟩
  intro _ _ _ _ V_δ
  classical
  obtain ⟨r⟩ := r
  obtain ⟨s⟩ := s
  obtain ⟨a⟩ := a
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω ↦ (ω t).2.2
  let _ : MeasurableSpace Θ := borel Θ
  have _ : BorelSpace Θ := ⟨rfl⟩
  have hr : ∀ θ' t, PSpace (M θ') (r t) := fun _ t =>
    ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩
  have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun θ' =>
    PSpace_Path.of.All_PSpace (hr θ')
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd h₁ t).aemeasurable⟩)
  let L : StrongDual ℝ Θ ≃L[ℝ] Θ := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv
  have hL : ∀ φ, (InnerProductSpace.toDual ℝ Θ).symm φ = L φ := fun _ => rfl
  have hφg : StronglyMeasurable
      (fun z : 𝒮 × 𝒜 => gradient (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ) := by
    simp only [gradient]
    exact ((InnerProductSpace.toDual ℝ Θ).symm.continuous.comp_stronglyMeasurable hφ)
  have hMsg : ∀ y u,
      ‖gradient (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms := fun y u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hMsle y u
  set ψ : 𝒮 → 𝒜 → Θ →L[ℝ] ℝ := fun y u =>
    fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ
  have hψ : StronglyMeasurable (Function.uncurry ψ) := hφ
  -- discounted return series swap
  have hRint : ∀ θ' : Θ, ∫ ω, ∑' t, γ ^ t * r t ω ∂(M θ') = ∑' t, γ ^ t * ∫ ω, r t ω ∂(M θ') := by
    intro θ'
    have hrb : ∀ t, ∀ᵐ ω ∂(M θ'), ‖γ ^ t * r t ω‖ ≤ γ ^ t * |M.env.R| := fun t =>
      (All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity h₁ (M := M) θ').mono fun ω h => by
        rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
        exact mul_le_mul_of_nonneg_left (h t) (pow_nonneg h₀.1 t)
    have hri : ∀ t, Integrable (fun ω => γ ^ t * r t ω) (M θ') := fun t =>
      Integrable.of_bound ((Random.Measurable.of.All_Eq.fst h₁ t).const_mul (γ ^ t)).aestronglyMeasurable
        _ (hrb t)
    rw [← integral_tsum_of_summable_integral_norm hri]
    · exact tsum_congr fun t => integral_const_mul _ _
    ·
      refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
        ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|)
      calc
        _ ≤ ∫ _, γ ^ t * |M.env.R| ∂(M θ') :=
          integral_mono_ae (hri t).norm (integrable_const _) (hrb t)
        _ = γ ^ t * |M.env.R| := by simp
  have hGet :=
    GetTSum_SMul.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
      (M := M) h₀ h₁ hπ h₂ h₃ h₄ h₅ θ
  have hEfun :
      (fun θ' ↦ 𝔼[r: M θ']((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r)) =
        (fun θ' ↦ ∑' t, γ ^ t * ∫ ω, r t ω ∂(M θ')) := by
    funext θ'
    have : PSpace (M θ') (AsPathRV.path r) :=
      PSpace_Path.of.All_PSpace (hr θ')
    refine (ExpectDotPow_Id.eq.Integral_ExtDotPow_Id.of.All_EqWithDensity
      (M := M) (θ := θ') (γ := γ) (r := r)).trans ?_
    simp only [Dot.dot, Function.hPow_apply, id_eq]
    exact hRint θ'
  have hLHS :
      ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
        L (∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ) := by
    simp only [gradient, hL]
    exact congrArg (fun f ↦ L (fderiv ℝ f θ)) hEfun ▸
      congrArg L hGet.fderiv.symm ▸ rfl
  -- ∑ γ^t • fderiv(∫r) = ∑ γ^t • ∫ (∑ γ^k δ) • fderiv log
  have hchain :
      ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ =
        ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
          M.V θ γ (t + k) (s (t + k) ω))) •
            fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
    have hTSum :=
      TSum_SMul.eq.Integral_Fderiv_Vkd.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
        (M := M) h₀ h₁ hπ h₂ h₃ h₄ h₅ θ
    have hQ :=
      Integral_Fderiv_Vkd.eq.TSum_SMul_Integral_SMul_Qkd_FderivLog.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_Eq_Joint.All_EqWithDensity
        (M := M) h₀ h₁ hπ h₂ h₃ h₄ h₅ hφ hMs
    refine hTSum.trans (hQ.trans (tsum_congr fun t => congrArg (fun z => γ ^ t • z) ?_))
    have hQδ :=
      Integral_SMul_Qkd.eq.Integral_SMul_SubAddVkd.of.In_Ico.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity
        (M := M) h₀ h₁ hπ h₂ h₃ h₄ hφ hMsle t
    have hcoll :=
      collapse_V0 (M := M) h₀ h₁ hπ θ h₀ t ψ hψ ⟨Ms, hMsle⟩
    -- `∫ Q • score = ∫ (∑ γ^k δ^{V0}) • score`, then rewrite to textbook-`V` residuals.
    have hQV0 := hQδ.trans hcoll.symm
    have hbridge :
        ∫ ω, (∑' k, γ ^ k * (r (t + k) ω + γ * M.V0 θ γ (s (t + k + 1) ω) -
          M.V0 θ γ (s (t + k) ω))) •
          fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) =
        ∫ ω, (∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
          M.V θ γ (t + k) (s (t + k) ω))) •
          fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
      set BV : ℝ := (1 - γ)⁻¹ * |M.env.R|
      have hBV0 : 0 ≤ BV :=
        mul_nonneg (inv_nonneg.2 (le_of_lt (sub_pos.2 h₀.2))) (abs_nonneg _)
      have hR0 : 0 ≤ |M.env.R| := abs_nonneg _
      have hr_bd : ∀ᵐ ω ∂(M θ), ∀ j, |r j ω| ≤ |M.env.R| := by
        have hcl : ∀ j,
            r j =ᵐ[M θ] fun ω => clip (ω j).1 (-M.env.R) M.env.R := fun j =>
          MEq_Clip.of.All_Eq.All_EqWithDensity h₁ (M := M) θ j
        have hcl' := (ae_all_iff (ι := ℕ)).mpr hcl
        filter_upwards [hcl'] with ω hω j
        rw [hω j, ← Real.norm_eq_abs]
        exact NormClip.le.Abs_R (R := M.env.R) (ρ := (ω j).1)
      have hVbd : ∀ᵐ ω ∂(M θ), ∀ n, |M.V θ γ n (s n ω)| ≤ BV := by
        have hδ' := ae_norm_residual (M := M) h₀ h₁ θ
        -- recover the pointwise `V` bound from the residual helper's proof style
        have hrm : ∀ k, Measurable (r k) := fun k => Random.Measurable.of.All_Eq.fst h₁ k
        have hsm : ∀ k, Measurable (s k) := fun k => Random.Measurable.of.All_Eq.snd.fst h₁ k
        have hpR : Measurable (fun ω i => r i ω) := Measurable.of_eval hrm
        have hfGret : ∀ k, Measurable
            (fun integ : ℕ → ℝ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) := fun k =>
          Measurable.tsum fun j => (measurable_pi_apply (k + j)).const_mul _
        have hret_bd : ∀ᵐ ω ∂(M θ), ∀ k,
            ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:])‖ ≤ BV := by
          have hgeo := (hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|
          filter_upwards [hr_bd] with ω hω k
          refine tsum_of_norm_bounded hgeo fun j => ?_
          have hid : (γ ^ (id : ℕ → ℕ)) j = γ ^ j := rfl
          have hslice : (fun i => r i ω)[k:] j = r (k + j) ω := rfl
          rw [hid, hslice, norm_mul, norm_pow, Real.norm_of_nonneg h₀.1, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hω (k + j)) (pow_nonneg h₀.1 j)
        have hret : ∀ k, Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
            (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:] := fun k =>
          (hfGret k).comp hpR
        have hGi : ∀ k,
            Integrable (fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:]) (M θ) :=
          fun k =>
            Integrable.of_bound (hret k).aestronglyMeasurable BV
              (by filter_upwards [hret_bd] with ω hω; exact hω k)
        have hV_ae : ∀ k,
            (fun ω => M.V θ γ k (s k ω)) =ᵐ[M θ]
              Expectation.condSigma (M θ) (fun ω i => r i ω) (s k)
                (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) := fun k => by
          have hcomp :=
            Expectation.condEval_comp_ae_eq_condSigma
              (x := fun ω i => r i ω) (y := s k)
              (f := fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:])
              hpR.aemeasurable (hsm k) (hfGret k).stronglyMeasurable (hGi k)
          filter_upwards [hcomp] with ω hω
          exact hω
        have hcond : ∀ k, ∀ᵐ ω ∂(M θ),
            |Expectation.condSigma (M θ) (fun ω i => r i ω) (s k)
              (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) ω| ≤ BV := fun k => by
          have hbd :=
            ae_bdd_norm_condExp_of_ae_bdd_norm
              (f := fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun i => r i ω)[k:])
              (m := MeasurableSpace.comap (s k) inferInstance)
              (by filter_upwards [hret_bd] with ω hω; exact hω k)
          filter_upwards [hbd] with ω h
          simpa [Expectation.condSigma, Real.norm_eq_abs] using h
        have hVeq := (ae_all_iff (ι := ℕ)).mpr hV_ae
        have hVnorm := (ae_all_iff (ι := ℕ)).mpr hcond
        filter_upwards [hVeq, hVnorm] with ω heq hnorm k
        rw [heq k]
        exact hnorm k
      have hV0bd : ∀ y, |M.V0 θ γ y| ≤ BV := fun y => by
        simpa [Real.norm_eq_abs, BV] using
          NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ θ y
      have hteleV0 : ∀ᵐ ω ∂(M θ),
          (∑' k, γ ^ k * (r (t + k) ω + γ * M.V0 θ γ (s (t + k + 1) ω) -
            M.V0 θ γ (s (t + k) ω))) =
            (∑' k, γ ^ k * r (t + k) ω) - M.V0 θ γ (s t ω) := by
        filter_upwards [hr_bd] with ω hr
        exact tsum_residual_eq_return_sub (fun _ x => M.V0 θ γ x) h₀ r s t ω
          hR0 hBV0 hr (fun n => hV0bd (s n ω))
      have hteleV : ∀ᵐ ω ∂(M θ),
          (∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
            M.V θ γ (t + k) (s (t + k) ω))) =
            (∑' k, γ ^ k * r (t + k) ω) - M.V θ γ t (s t ω) := by
        filter_upwards [hr_bd, hVbd] with ω hr hv
        exact tsum_residual_eq_return_sub (fun n x => M.V θ γ n x) h₀ r s t ω
          hR0 hBV0 hr (fun n => hv n)
      have hdiff : ∀ᵐ ω ∂(M θ),
          (∑' k, γ ^ k * (r (t + k) ω + γ * M.V0 θ γ (s (t + k + 1) ω) -
            M.V0 θ γ (s (t + k) ω))) -
          (∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
            M.V θ γ (t + k) (s (t + k) ω))) =
            M.V θ γ t (s t ω) - M.V0 θ γ (s t ω) := by
        filter_upwards [hteleV0, hteleV] with ω h0 hv
        rw [h0, hv]
        ring
      have hclip_le : ∀ x, |clip x (-BV) BV| ≤ BV := fun x => by
        have hlo : -BV ≤ clip x (-BV) BV := by
          simp only [clip]
          exact le_min (le_max_right _ _) (neg_le_self hBV0)
        have hhi : clip x (-BV) BV ≤ BV := by
          simp only [clip]
          exact min_le_right _ _
        exact abs_le.2 ⟨hlo, hhi⟩
      let hh : 𝒮 → ℝ := fun y => clip (M.V θ γ t y) (-BV) BV - M.V0 θ γ y
      have hhmeas : Measurable hh := by
        have hclipm : Measurable fun x : ℝ => clip x (-BV) BV := by
          simp only [clip]
          exact (continuous_min.comp
            ((continuous_max.comp (continuous_id.prodMk continuous_const)).prodMk
              continuous_const)).measurable
        change Measurable fun y => clip (M.V θ γ t y) (-BV) BV - M.V0 θ γ y
        exact (hclipm.comp ((hVm (t)))).sub
          (Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ)
      have hhC : ∀ y, ‖hh y‖ ≤ 2 * BV := fun y => by
        rw [Real.norm_eq_abs]
        have h2 : |clip (M.V θ γ t y) (-BV) BV - M.V0 θ γ y| ≤
            |clip (M.V θ γ t y) (-BV) BV| + |M.V0 θ γ y| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le (clip (M.V θ γ t y) (-BV) BV) (-M.V0 θ γ y)
        have := h2.trans (add_le_add (hclip_le (M.V θ γ t y)) (hV0bd y))
        simpa [hh, two_mul] using this
      have hsc :=
        Integral_SMul.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity
          (M := M) θ h₁ h₂ h₃ h₄ hh hhmeas hhC hφ hMsle t
      have hclip : ∀ᵐ ω ∂(M θ),
          clip (M.V θ γ t (s t ω)) (-BV) BV = M.V θ γ t (s t ω) := by
        filter_upwards [hVbd] with ω hv
        have hlo : -BV ≤ M.V θ γ t (s t ω) := (abs_le.1 (hv t)).1
        have hhi : M.V θ γ t (s t ω) ≤ BV := (abs_le.1 (hv t)).2
        rw [clip, max_eq_left hlo, min_eq_left hhi]
      have hae : ∀ᵐ ω ∂(M θ),
          (∑' k, γ ^ k * (r (t + k) ω + γ * M.V0 θ γ (s (t + k + 1) ω) -
            M.V0 θ γ (s (t + k) ω))) •
            fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ -
          (∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
            M.V θ γ (t + k) (s (t + k) ω))) •
            fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ =
          hh (s t ω) •
            fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ := by
        filter_upwards [hdiff, hclip] with ω hd hc
        rw [← sub_smul, hd]
        simp only [hh, hc]
      set F0 : (ℕ → ℝ × 𝒮 × 𝒜) → Θ →L[ℝ] ℝ := fun ω =>
        (∑' k, γ ^ k * (r (t + k) ω + γ * M.V0 θ γ (s (t + k + 1) ω) -
          M.V0 θ γ (s (t + k) ω))) •
          fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ
      set FV : (ℕ → ℝ × 𝒮 × 𝒜) → Θ →L[ℝ] ℝ := fun ω =>
        (∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
          M.V θ γ (t + k) (s (t + k) ω))) •
          fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ
      set B1 : ℝ := (2 / (1 - γ)) * |M.env.R|
      set Bsum : ℝ := (2 / (1 - γ) ^ 2) * |M.env.R|
      have hgeo1 := (hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right B1
      have hδall := ae_norm_residual (M := M) h₀ h₁ θ
      have hFVbd : ∀ᵐ ω ∂(M θ), ‖FV ω‖ ≤ Bsum * Ms := by
        filter_upwards [hδall] with ω h
        have hs : Summable fun k : ℕ =>
            ‖γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
              M.V θ γ (t + k) (s (t + k) ω))‖ :=
          Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
            (fun k => by
              rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
              exact mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg h₀.1 k))
            hgeo1.summable
        have hts : ‖∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
            M.V θ γ (t + k) (s (t + k) ω))‖ ≤ Bsum := by
          refine (norm_tsum_le_tsum_norm hs).trans ?_
          have hpt : ∀ k,
              ‖γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
                M.V θ γ (t + k) (s (t + k) ω))‖ ≤ γ ^ k * B1 := fun k => by
            rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
            exact mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg h₀.1 k)
          have htendB : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, γ ^ i * B1) atTop
              (nhds (∑' k, γ ^ k * B1)) := by
            simpa [hgeo1.tsum_eq] using hgeo1.tendsto_sum_nat
          have hsumle :
              (∑' k, ‖γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
                M.V θ γ (t + k) (s (t + k) ω))‖) ≤ ∑' k, γ ^ k * B1 :=
            le_of_tendsto_of_tendsto hs.hasSum.tendsto_sum_nat htendB
              (Filter.Eventually.of_forall fun N =>
                Finset.sum_le_sum fun k _ => hpt k)
          have heq : ∑' k, γ ^ k * B1 = (1 - γ)⁻¹ * B1 := hgeo1.tsum_eq
          have hB : (1 - γ)⁻¹ * B1 = Bsum := by
            simp only [B1, Bsum, div_eq_mul_inv]
            rw [← inv_pow]
            ring
          exact hsumle.trans (heq.trans hB).le
        have : ‖FV ω‖ ≤ Bsum * Ms := by
          dsimp only [FV]
          rw [norm_smul]
          exact mul_le_mul hts (hMsle (s t ω) (a t ω)) (norm_nonneg _)
            ((norm_nonneg _).trans hts)
        exact this
      have hF0bd : ∀ᵐ ω ∂(M θ), ‖F0 ω‖ ≤
          ((1 - γ)⁻¹ * ((3 / (1 - γ) - 1) * |M.env.R|)) * Ms := by
        have hbd0 :=
          AeAll_LeNorm_TSum_MulPowSubAddRMul_VkdVkdMulSub1DeltaBound.of.In_Ico.In_Ico.All_EqWithDensity
            (M := M) h₀ h₁ h₀ θ
        filter_upwards [hbd0] with ω h
        dsimp only [F0]
        rw [norm_smul]
        exact mul_le_mul (h t) (hMsle (s t ω) (a t ω)) (norm_nonneg _)
          ((norm_nonneg _).trans (h t))
      have hF0m : AEStronglyMeasurable F0 (M θ) := by
        have hcoeff0 : Measurable fun ω =>
            ∑' k, γ ^ k * (r (t + k) ω + γ * M.V0 θ γ (s (t + k + 1) ω) -
              M.V0 θ γ (s (t + k) ω)) := by
          refine Measurable.tsum fun k => ?_
          exact (((Random.Measurable.of.All_Eq.fst h₁ (t + k)).add
            (((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp
                (Random.Measurable.of.All_Eq.snd.fst h₁ (t + k + 1))).const_mul γ)).sub
            ((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp
              (Random.Measurable.of.All_Eq.snd.fst h₁ (t + k)))).const_mul _
        have hscore : StronglyMeasurable fun ω =>
            fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ :=
          hφ.comp_measurable
            ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
              (Random.Measurable.of.All_Eq.snd.snd h₁ t))
        have hsm0 : StronglyMeasurable F0 := by
          simp only [F0]
          convert hcoeff0.stronglyMeasurable.smul hscore
        exact hsm0.aestronglyMeasurable
      have hFVm : AEStronglyMeasurable FV (M θ) := by
        have hcoeffV : Measurable fun ω =>
            ∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
              M.V θ γ (t + k) (s (t + k) ω)) := by
          refine Measurable.tsum fun k => ?_
          exact (((Random.Measurable.of.All_Eq.fst h₁ (t + k)).add
            ((((hVm (t + k + 1))).comp
                (Random.Measurable.of.All_Eq.snd.fst h₁ (t + k + 1))).const_mul γ)).sub
            (((hVm (t + k))).comp
              (Random.Measurable.of.All_Eq.snd.fst h₁ (t + k)))).const_mul _
        have hscore : StronglyMeasurable fun ω =>
            fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ :=
          hφ.comp_measurable
            ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
              (Random.Measurable.of.All_Eq.snd.snd h₁ t))
        have hsmV : StronglyMeasurable FV := by
          simp only [FV]
          convert hcoeffV.stronglyMeasurable.smul hscore
        exact hsmV.aestronglyMeasurable
      have hF0i : Integrable F0 (M θ) :=
        Integrable.of_bound hF0m _ hF0bd
      have hFVi : Integrable FV (M θ) :=
        Integrable.of_bound hFVm _ hFVbd
      have hsub : ∫ ω, F0 ω ∂(M θ) - ∫ ω, FV ω ∂(M θ) =
          ∫ ω, hh (s t ω) •
            fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
        rw [← integral_sub hF0i hFVi]
        exact integral_congr_ae hae
      have := hsub.trans hsc
      exact sub_eq_zero.mp this
    exact hQV0.trans hbridge
  have hmeas : ∀ k, Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
      (fun (s : ℕ → 𝒮) (_ : ℕ → 𝒜) (r : ℕ → ℝ) (k : ℕ) =>
          r k + γ * M.V θ γ (k + 1) (s (k + 1)) - M.V θ γ k (s k))
        (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) k := fun k =>
    ((Random.Measurable.of.All_Eq.fst h₁ k).add
      ((((hVm (k + 1))).comp
          (Random.Measurable.of.All_Eq.snd.fst h₁ (k + 1))).const_mul γ)).sub
      (((hVm (k))).comp
        (Random.Measurable.of.All_Eq.snd.fst h₁ k))
  have hδall := ae_norm_residual (M := M) h₀ h₁ θ
  set B1 : ℝ := (2 / (1 - γ)) * |M.env.R|
  set Bδ : ℝ := (2 / (1 - γ) ^ 2) * |M.env.R|
  have hgeo1 := (hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right B1
  have hbd : ∀ᵐ ω ∂(M θ), ∀ t,
      ‖∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
        M.V θ γ (t + k) (s (t + k) ω))‖ ≤ Bδ := by
    filter_upwards [hδall] with ω h t
    have hs : Summable fun k : ℕ =>
        ‖γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
          M.V θ γ (t + k) (s (t + k) ω))‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun k => by
          rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
          exact mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg h₀.1 k))
        hgeo1.summable
    refine (norm_tsum_le_tsum_norm hs).trans ?_
    have hpt : ∀ k,
        ‖γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
          M.V θ γ (t + k) (s (t + k) ω))‖ ≤ γ ^ k * B1 := fun k => by
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg h₀.1 k)
    have htendB : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, γ ^ i * B1) atTop
        (nhds (∑' k, γ ^ k * B1)) := by
      simpa [hgeo1.tsum_eq] using hgeo1.tendsto_sum_nat
    have hsumle :
        (∑' k, ‖γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
          M.V θ γ (t + k) (s (t + k) ω))‖) ≤ ∑' k, γ ^ k * B1 :=
      le_of_tendsto_of_tendsto hs.hasSum.tendsto_sum_nat htendB
        (Filter.Eventually.of_forall fun N =>
          Finset.sum_le_sum fun k _ => hpt k)
    have heq : ∑' k, γ ^ k * B1 = (1 - γ)⁻¹ * B1 := hgeo1.tsum_eq
    have hB : (1 - γ)⁻¹ * B1 = Bδ := by
      simp only [B1, Bδ, div_eq_mul_inv]
      rw [← inv_pow]
      ring
    exact hsumle.trans (heq.trans hB).le
  have hAdvExp :=
    Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.All_Eq_Joint.All_EqWithDensity
      (M := M) (θ := θ) (γ := γ)
      (X := fun s _ r k => r k + γ * M.V θ γ (k + 1) (s (k + 1)) - M.V θ γ k (s k))
      (B := Bδ) (Ms := Ms) h₀ h₁ hmeas hbd hφg hMsg
  refine hLHS.trans ((congrArg L hchain).trans (hAdvExp.trans ?_))
  -- rewrite ∑' sugar into Dot / V_δ form
  refine congrArg
    (Expectation.ofRV (M θ)
      (JointRandomSymbol (Expectation.asRV r)
        (JointRandomSymbol (Expectation.asRV s) (Expectation.asRV a)))) ?_
  funext integ
  -- LHS: ∑' γ^t • (((γ^k) ⬝ᵥ δ) • ∇log); RHS: (γ^id) ⬝ᵥ fun t ↦ (((γ^id) ⬝ᵥ δ_Vθ) • ∇log)
  change
      (∑' t, γ ^ t •
          (((fun k : ℕ => γ ^ k) ⬝ᵥ
              (fun k => integ.1 (t + k) + γ * M.V θ γ (t + k + 1) (integ.2.1 (t + k + 1)) -
                M.V θ γ (t + k) (integ.2.1 (t + k)))) •
            ∇[θ] Real.log (M.policy.prob θ (integ.2.1 t) (integ.2.2 t)))) =
        ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
          (((γ ^ (id : ℕ → ℕ)) ⬝ᵥ
              ((fun k => integ.1 (t + k)) +
                γ • (fun k => V_δ[t + 1] (fun j => integ.2.1 (t + 1 + j)) k) -
                fun k => V_δ[t] (fun j => integ.2.1 (t + j)) k)) •
            ∇[θ] Real.log (M.policy.prob θ (integ.2.1 t) (integ.2.2 t))))
  simp only [Dot.dot, Function.hPow_apply, id_eq]
  refine tsum_congr fun t => ?_
  congr 1
  congr 1
  refine tsum_congr fun k => ?_
  have hk : t + k + 1 = t + 1 + k := by omega
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, V_δ, hk]


-- created on 2026-10-20
-- updated on 2026-11-14
