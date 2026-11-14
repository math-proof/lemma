import Lemma.Kernel.Integral.eq.Integral_Integral.of.Integrable_Bind
import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Kf.eq.Integral.All_EqWithDensity
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Vkd.eq.Integral_MulProbQkd.of.In_Ico.All_Measurable_Prob
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.Measurable_Wkd.of.All_Measurable_Prob
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Random.NormWkd.le.Abs_R
import Lemma.Random.NormClip.le.Abs_R
import Lemma.Real.NormIntegral.le.of.All_LeNormMul.EqIntegral_1
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Real Kernel
set_option maxHeartbeats 800000


private lemma stage_clip
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜} {θ : Θ} (y : 𝒮) :
  ∫ w, clip w.1 (-M.env.R) M.env.R ∂(M.stageK θ y) = M.Wkd θ 0 y := by
  have := M.env.reward_markov
  have hf : StronglyMeasurable fun w : ℝ × 𝒮 × 𝒜 ↦ clip w.1 (-M.env.R) M.env.R :=
    ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hC : ∀ (w : ℝ × 𝒮 × 𝒜), ‖clip w.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
    fun w => NormClip.le.Abs_R M.env.R w.1
  have e :=
    Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ y
  refine e.trans ?_
  simp only [DensityModel.Wkd, DensityModel.rkd, smul_eq_mul]


private lemma stage_Vkd
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜} {θ : Θ} {γ : ℝ}
  (h₀ : γ ∈ Set.Ico 0 1)
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 ↦ M.policy.prob θ z.1 z.2))
  (y : 𝒮) :
  ∫ w, M.V0 θ γ w.2.1 ∂(M.stageK θ y) = M.V0 θ γ y := by
  have := M.env.reward_markov
  have hf : StronglyMeasurable fun w : ℝ × 𝒮 × 𝒜 ↦ M.V0 θ γ w.2.1 :=
    ((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp measurable_snd.fst).stronglyMeasurable
  have hC : ∀ (w : ℝ × 𝒮 × 𝒜), ‖M.V0 θ γ w.2.1‖ ≤ (1 - γ)⁻¹ * |M.env.R| :=
    fun w => NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ θ w.2.1
  have e :=
    Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ y
  refine e.trans ?_
  change ∫ u, M.policy.prob θ y u •
      (∫ ρ, M.V0 θ γ y ∂(M.env.reward (y, u)))
      ∂ReferenceMeasure.measure = _
  have hconst : ∀ u,
      ∫ ρ, M.V0 θ γ y ∂(M.env.reward (y, u)) = M.V0 θ γ y := fun u => by
    have : IsProbabilityMeasure (M.env.reward (y, u)) := inferInstance
    rw [MeasureTheory.integral_const, probReal_univ, one_smul]
  simp_rw [hconst]
  change ∫ u, M.policy.prob θ y u • M.V0 θ γ y ∂ReferenceMeasure.measure = _
  rw [integral_smul_const, M.policy.integral_eq_one θ y, one_smul]


private lemma Kf_clip_one
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜} {θ : Θ} (z : ℝ × 𝒮 × 𝒜) :
  M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) 1 z =
    ∫ y, M.Wkd θ 0 y ∂(M.env.trans z.2) := by
  have := M.env.trans_markov
  have := M.env.reward_markov
  rw [Kf.eq.Integral.All_EqWithDensity (M := M) θ 0 z]
  unfold DensityModel.K
  rw [Kernel.comp_apply, Kernel.comap_apply]
  change ∫ w, clip w.1 (-M.env.R) M.env.R ∂(M.stageK θ ∘ₘ M.env.trans z.2) = _
  have hf : StronglyMeasurable fun w : ℝ × 𝒮 × 𝒜 ↦ clip w.1 (-M.env.R) M.env.R :=
    ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hC : ∀ (w : ℝ × 𝒮 × 𝒜), ‖clip w.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
    fun w => NormClip.le.Abs_R M.env.R w.1
  have hbind : Integrable (fun w ↦ clip w.1 (-M.env.R) M.env.R)
      (M.stageK θ ∘ₘ (M.env.trans z.2)) :=
    Integrable.of_bound hf.aestronglyMeasurable _ (Filter.Eventually.of_forall hC)
  rw [Integral.eq.Integral_Integral.of.Integrable_Bind hbind]
  simp_rw [stage_clip]


private lemma Kf_Vkd_one
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜} {θ : Θ} {γ : ℝ}
  (h₀ : γ ∈ Set.Ico 0 1)
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 ↦ M.policy.prob θ z.1 z.2))
  (z : ℝ × 𝒮 × 𝒜) :
  M.Kf θ (fun w ↦ M.V0 θ γ w.2.1) 1 z =
    ∫ y, M.V0 θ γ y ∂(M.env.trans z.2) := by
  have := M.env.trans_markov
  have := M.env.reward_markov
  rw [Kf.eq.Integral.All_EqWithDensity (M := M) θ 0 z]
  unfold DensityModel.K
  rw [Kernel.comp_apply, Kernel.comap_apply]
  change ∫ w, M.V0 θ γ w.2.1 ∂(M.stageK θ ∘ₘ M.env.trans z.2) = _
  have hf : StronglyMeasurable fun w : ℝ × 𝒮 × 𝒜 ↦ M.V0 θ γ w.2.1 :=
    ((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp measurable_snd.fst).stronglyMeasurable
  have hC : ∀ (w : ℝ × 𝒮 × 𝒜), ‖M.V0 θ γ w.2.1‖ ≤ (1 - γ)⁻¹ * |M.env.R| :=
    fun w => NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ θ w.2.1
  have hbind : Integrable (fun w ↦ M.V0 θ γ w.2.1)
      (M.stageK θ ∘ₘ (M.env.trans z.2)) :=
    Integrable.of_bound hf.aestronglyMeasurable _ (Filter.Eventually.of_forall hC)
  rw [Integral.eq.Integral_Integral.of.Integrable_Bind hbind]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => stage_Vkd (M := M) h₀ hπ y)


/--
Bellman identity for continuous-action kernel expectations.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 ↦ M.policy.prob θ z.1 z.2))
  (θ : Θ)
  (z : ℝ × 𝒮 × 𝒜) :
-- imply
  M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) 1 z +
      γ * M.Kf θ (fun w ↦ M.V0 θ γ w.2.1) 2 z -
      M.Kf θ (fun w ↦ M.V0 θ γ w.2.1) 1 z = 0 := by
-- proof
  classical
  have := M.env.trans_markov
  have := M.env.reward_markov
  set f : ℝ × 𝒮 × 𝒜 → ℝ := fun w ↦ M.V0 θ γ w.2.1
  have hf : StronglyMeasurable f :=
    ((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp measurable_snd.fst).stronglyMeasurable
  have hC : ∀ (w : ℝ × 𝒮 × 𝒜), ‖f w‖ ≤ (1 - γ)⁻¹ * |M.env.R| :=
    fun w => NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ θ w.2.1
  have h1 := Kf_clip_one (M := M) (θ := θ) z
  have h3 := Kf_Vkd_one (M := M) (θ := θ) h₀ hπ z
  have hKf1w : ∀ w, M.Kf θ f 1 w = ∫ y, M.V0 θ γ y ∂(M.env.trans w.2) :=
    fun w => Kf_Vkd_one (M := M) (θ := θ) h₀ hπ w
  have h2 : M.Kf θ f 2 z =
      ∫ y, (∫ u, M.policy.prob θ y u *
        (∫ y', M.V0 θ γ y' ∂(M.env.trans (y, u))) ∂ReferenceMeasure.measure)
        ∂(M.env.trans z.2) := by
    rw [Kf.eq.Integral.All_EqWithDensity (M := M) θ 1 z]
    unfold DensityModel.K
    rw [Kernel.comp_apply, Kernel.comap_apply]
    have hsm := (StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ 1).1
    have hbd := (StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ 1).2
    have hbind : Integrable (M.Kf θ f 1) (M.stageK θ ∘ₘ (M.env.trans z.2)) :=
      Integrable.of_bound hsm.aestronglyMeasurable _ (Filter.Eventually.of_forall hbd)
    rw [Integral.eq.Integral_Integral.of.Integrable_Bind hbind]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hTsm : StronglyMeasurable
        (fun w : ℝ × 𝒮 × 𝒜 ↦ ∫ y', M.V0 θ γ y' ∂(M.env.trans w.2)) :=
      ((StronglyMeasurable.integral_kernel_prod_right'
        (κ := M.env.trans) (f := fun p : (𝒮 × 𝒜) × 𝒮 ↦ M.V0 θ γ p.2)
        ((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp measurable_snd).stronglyMeasurable).comp_measurable
        (measurable_snd : Measurable fun w : ℝ × 𝒮 × 𝒜 ↦ w.2))
    have hTC : ∀ (w : ℝ × 𝒮 × 𝒜), ‖∫ y', M.V0 θ γ y' ∂(M.env.trans w.2)‖ ≤
        (1 - γ)⁻¹ * |M.env.R| :=
      fun w => (norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall fun y' =>
          NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ θ y')).trans_eq (by simp)
    have e :=
      Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hTsm hTC θ y
    have e0 :
        ∫ w, M.Kf θ f 1 w ∂(M.stageK θ y) =
          ∫ w, (∫ y', M.V0 θ γ y' ∂(M.env.trans w.2)) ∂(M.stageK θ y) :=
      integral_congr_ae (Filter.Eventually.of_forall fun w => hKf1w w)
    refine e0.trans (e.trans ?_)
    have hρ : ∀ u,
        ∫ ρ, (∫ y', M.V0 θ γ y' ∂(M.env.trans (y, u)))
          ∂(M.env.reward (y, u)) =
          ∫ y', M.V0 θ γ y' ∂(M.env.trans (y, u)) := fun u => by
      have : IsProbabilityMeasure (M.env.reward (y, u)) := inferInstance
      rw [MeasureTheory.integral_const, probReal_univ, one_smul]
    change ∫ u, M.policy.prob θ y u •
        (∫ ρ, (∫ y', M.V0 θ γ y' ∂(M.env.trans (y, u)))
          ∂(M.env.reward (y, u)))
        ∂ReferenceMeasure.measure = _
    simp_rw [hρ, smul_eq_mul]
  rw [h1, h2, h3]
  have hBell : ∀ y,
      M.Wkd θ 0 y + γ * (∫ u, M.policy.prob θ y u *
          (∫ y', M.V0 θ γ y' ∂(M.env.trans (y, u))) ∂ReferenceMeasure.measure) -
        M.V0 θ γ y = 0 := by
    intro y
    have hV := Vkd.eq.Integral_MulProbQkd.of.In_Ico.All_Measurable_Prob (M := M) hπ h₀ θ y
    have hW0 : M.Wkd θ 0 y =
        ∫ u, M.policy.prob θ y u * M.rkd y u ∂ReferenceMeasure.measure := by
      simp [DensityModel.Wkd]
    linarith [hV, hW0]
  have hW : Integrable (M.Wkd θ 0) (M.env.trans z.2) :=
    Integrable.of_bound (Measurable_Wkd.of.All_Measurable_Prob (M := M) hπ θ 0).aestronglyMeasurable
      |M.env.R| (Filter.Eventually.of_forall fun y => NormWkd.le.Abs_R (M := M) θ 0 y)
  have hVint : Integrable (M.V0 θ γ) (M.env.trans z.2) :=
    Integrable.of_bound (Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).aestronglyMeasurable
      ((1 - γ)⁻¹ * |M.env.R|)
      (Filter.Eventually.of_forall fun y => NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ θ y)
  have hGbd : ∀ y, ‖∫ u, M.policy.prob θ y u *
        (∫ y', M.V0 θ γ y' ∂(M.env.trans (y, u))) ∂ReferenceMeasure.measure‖
      ≤ (1 - γ)⁻¹ * |M.env.R| := fun y => by
    have hBound := (1 - γ)⁻¹ * |M.env.R|
    apply NormIntegral.le.of.All_LeNormMul.EqIntegral_1 (M.policy.integral_eq_one θ y)
    intro u
    have hp : 0 ≤ M.policy.prob θ y u := M.policy.nonneg θ y u
    rw [norm_mul, Real.norm_of_nonneg hp]
    exact mul_le_mul_of_nonneg_left
      ((norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall fun y' =>
          NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ θ y')).trans_eq (by simp))
      hp
  have hGin : AEStronglyMeasurable
      (fun y : 𝒮 ↦ ∫ u, M.policy.prob θ y u *
        (∫ y', M.V0 θ γ y' ∂(M.env.trans (y, u))) ∂ReferenceMeasure.measure)
      (M.env.trans z.2) := by
    have hp : Measurable (fun z : 𝒮 × 𝒜 ↦ M.policy.prob θ z.1 z.2) := hπ θ
    have hT : StronglyMeasurable (fun z : 𝒮 × 𝒜 ↦
        ∫ y', M.V0 θ γ y' ∂(M.env.trans z)) :=
      StronglyMeasurable.integral_kernel_prod_right'
        (κ := M.env.trans) (f := fun p : (𝒮 × 𝒜) × 𝒮 ↦ M.V0 θ γ p.2)
        ((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp measurable_snd).stronglyMeasurable
    exact ((hp.stronglyMeasurable.mul hT).integral_prod_right).aestronglyMeasurable
  have hG : Integrable
      (fun y ↦ ∫ u, M.policy.prob θ y u *
        (∫ y', M.V0 θ γ y' ∂(M.env.trans (y, u))) ∂ReferenceMeasure.measure)
      (M.env.trans z.2) :=
    Integrable.of_bound hGin _ (Filter.Eventually.of_forall hGbd)
  have hγG := hG.const_mul γ
  have eγ :
      γ * ∫ y, (∫ u, M.policy.prob θ y u *
          (∫ y', M.V0 θ γ y' ∂(M.env.trans (y, u))) ∂ReferenceMeasure.measure)
        ∂(M.env.trans z.2) =
        ∫ y, γ * (∫ u, M.policy.prob θ y u *
          (∫ y', M.V0 θ γ y' ∂(M.env.trans (y, u))) ∂ReferenceMeasure.measure)
        ∂(M.env.trans z.2) :=
    (integral_const_mul _ _).symm
  have hLHS :
      ∫ y, M.Wkd θ 0 y ∂(M.env.trans z.2) +
        γ * ∫ y, (∫ u, M.policy.prob θ y u *
            (∫ y', M.V0 θ γ y' ∂(M.env.trans (y, u))) ∂ReferenceMeasure.measure)
          ∂(M.env.trans z.2) -
        ∫ y, M.V0 θ γ y ∂(M.env.trans z.2) =
      ∫ y, (M.Wkd θ 0 y + γ * (∫ u, M.policy.prob θ y u *
            (∫ y', M.V0 θ γ y' ∂(M.env.trans (y, u))) ∂ReferenceMeasure.measure) -
          M.V0 θ γ y) ∂(M.env.trans z.2) := by
    rw [eγ]
    set g : 𝒮 → ℝ := fun y =>
      γ * (∫ u, M.policy.prob θ y u *
        (∫ y', M.V0 θ γ y' ∂(M.env.trans (y, u))) ∂ReferenceMeasure.measure)
    change ∫ y, M.Wkd θ 0 y ∂(M.env.trans z.2) + ∫ y, g y ∂(M.env.trans z.2) -
        ∫ y, M.V0 θ γ y ∂(M.env.trans z.2) =
      ∫ y, (M.Wkd θ 0 y + g y - M.V0 θ γ y) ∂(M.env.trans z.2)
    have hg : Integrable g (M.env.trans z.2) := hγG
    have hadd := (integral_add hW hg).symm
    have hsub :=
      (integral_sub (μ := M.env.trans z.2) (f := fun y => M.Wkd θ 0 y + g y)
        (g := M.V0 θ γ) (hW.add hg) hVint).symm
    refine (congrArg₂ (· - ·) hadd rfl).trans ?_
    refine hsub.trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [sub_eq_add_neg, add_assoc]
  rw [hLHS]
  refine (integral_congr_ae (Filter.Eventually.of_forall hBell)).trans ?_
  simp


-- created on 2026-10-20
-- updated on 2026-11-12
