import Lemma.Random.NormClip.le.Abs_R
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.WAdd_1.eq.Integral_MulProbIntegral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Real.NormIntegral.le.of.All_LeNormMul.EqIntegral_1
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Real


/--
Bellman equation of the time-free value series in the continuous-action trajectory model:
`∑' k, γ ^ k * ∫ z, Kf θ (clip) k z ∂(stageK θ x) = ∫ z, Kf θ (clip) 0 z ∂(stageK θ x) +
  γ * ∫ u, π_θ(u | x) * ∫ y, (∑' k, γ ^ k * ∫ z, Kf θ (clip) k z ∂(stageK θ y)) ∂T(x, u) ∂μ`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮]
  [μ : ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (x : 𝒮) :
-- imply
  ∑' k, γ ^ k * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ x) =
    ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 0 z ∂(M.stageK θ x) +
      γ * ∫ u, M.policy.prob θ x u *
        (∫ y, (∑' k, γ ^ k *
          ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ y))
          ∂(M.env.trans (x, u))) ∂μ.measure := by
-- proof
  have := M.env.trans_markov
  have hclip : StronglyMeasurable
    (fun z : ℝ × 𝒮 × 𝒜 => clip z.1 (-M.env.R) M.env.R) := by
    unfold clip
    apply ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hbound : ∀ z : ℝ × 𝒮 × 𝒜, ‖clip z.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
    fun z => NormClip.le.Abs_R M.env.R z.1
  have hK := fun k =>
    StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hclip hbound θ k
  have hW : ∀ y k,
    ‖∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ y)‖ ≤
      |M.env.R| := fun y k => by
    have : IsProbabilityMeasure (M.stageK θ y) := inferInstance
    have h :=
      norm_integral_le_of_norm_le_const (μ := M.stageK θ y)
        (Filter.Eventually.of_forall (hK k).2)
    rwa [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] at h
  have hsum : ∀ y, Summable (fun k =>
    γ ^ k * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z
      ∂(M.stageK θ y)) := fun y => by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|) ?_
    intro k
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
    apply mul_le_mul_of_nonneg_left (hW y k) (pow_nonneg h₀.1 k)
  rw [(hsum x).tsum_eq_zero_add, pow_zero, one_mul]
  congr 1
  simp_rw [WAdd_1.eq.Integral_MulProbIntegral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hclip hbound θ, pow_succ, mul_comm _ γ, mul_assoc γ]
  rw [tsum_mul_left]
  congr 1
  let W : ℕ → 𝒮 → ℝ := fun k y =>
    ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ y)
  have hWm : ∀ k, Measurable (W k) := fun k =>
    (StronglyMeasurable.integral_kernel_prod_right' (κ := M.stageK θ)
      (f := fun p : 𝒮 × (ℝ × 𝒮 × 𝒜) =>
        M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k p.2)
      ((hK k).1.comp_measurable measurable_snd)).measurable
  have hb : ∀ k y, ‖γ ^ k * W k y‖ ≤ γ ^ k * |M.env.R| := fun k y => by
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
    apply mul_le_mul_of_nonneg_left (hW y k) (pow_nonneg h₀.1 k)
  have hinner : ∀ u,
    ∑' k, γ ^ k * ∫ y, W k y ∂(M.env.trans (x, u)) =
      ∫ y, (∑' k, γ ^ k * W k y) ∂(M.env.trans (x, u)) := by
    intro u
    have hri : ∀ k, Integrable (fun y => γ ^ k * W k y) (M.env.trans (x, u)) :=
      fun k => Integrable.of_bound ((hWm k).const_mul (γ ^ k)).aestronglyMeasurable
        (γ ^ k * |M.env.R|) (Filter.Eventually.of_forall (hb k))
    have hsn : Summable (fun k =>
      ∫ y, ‖γ ^ k * W k y‖ ∂(M.env.trans (x, u))) := by
      refine Summable.of_norm_bounded
        ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|) fun k => ?_
      have h :=
        norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u))
          (Filter.Eventually.of_forall fun y =>
            (norm_norm (γ ^ k * W k y)).symm ▸ hb k y)
      rwa [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] at h
    exact (tsum_congr fun k => (integral_const_mul (γ ^ k) (W k)).symm).trans
      (integral_tsum_of_summable_integral_norm hri hsn)
  have hπ : Integrable (M.policy.prob θ x) μ.measure := by
    apply Integrable.of_integral_ne_zero
    rw [M.policy.integral_eq_one θ x]
    apply one_ne_zero
  have hπm : Measurable (M.policy.prob θ x) :=
    (M.policy.measurable_prob θ).comp measurable_prodMk_left
  have hT : ∀ k, Measurable (fun u => ∫ y, W k y ∂(M.env.trans (x, u))) :=
    fun k =>
      ((StronglyMeasurable.integral_kernel_prod_right' (κ := M.env.trans)
        (f := fun z => W k z.2)
        ((hWm k).stronglyMeasurable.comp_measurable measurable_snd)).measurable).comp
        measurable_prodMk_left
  have hFb : ∀ k u,
    ‖M.policy.prob θ x u * (γ ^ k * ∫ y, W k y ∂(M.env.trans (x, u)))‖ ≤
      M.policy.prob θ x u * (γ ^ k * |M.env.R|) := fun k u => by
    have h :=
      norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u))
        (Filter.Eventually.of_forall fun y => hW y k)
    rw [norm_mul, Real.norm_of_nonneg (M.policy.nonneg θ x u), norm_mul, norm_pow,
      Real.norm_of_nonneg h₀.1]
    apply mul_le_mul_of_nonneg_left _ (M.policy.nonneg θ x u)
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg h₀.1 k)
    simpa using h
  have hFi : ∀ k, Integrable
    (fun u => M.policy.prob θ x u * (γ ^ k * ∫ y, W k y ∂(M.env.trans (x, u))))
    μ.measure := fun k =>
    (hπ.mul_const _).mono' (hπm.mul ((hT k).const_mul _)).aestronglyMeasurable
      (Filter.Eventually.of_forall (hFb k))
  have hFs : Summable (fun k =>
    ∫ u, ‖M.policy.prob θ x u * (γ ^ k * ∫ y, W k y ∂(M.env.trans (x, u)))‖
      ∂μ.measure) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|) fun k => ?_
    apply NormIntegral.le.of.All_LeNormMul.EqIntegral_1 (M.policy.integral_eq_one θ x)
    intro u
    simpa [norm_norm] using hFb k u
  calc
    _ = ∑' k, ∫ (u : 𝒜), (M.policy.prob θ x u *
      (γ ^ k * ∫ y, W k y ∂(M.env.trans (x, u)))) ∂μ.measure :=
      tsum_congr fun k => by
        rw [← integral_const_mul]
        congr 1
        funext u
        ring
    _ = ∫ (u : 𝒜), (∑' k, M.policy.prob θ x u *
      (γ ^ k * ∫ y, W k y ∂(M.env.trans (x, u)))) ∂μ.measure :=
      integral_tsum_of_summable_integral_norm hFi hFs
    _ = ∫ (u : 𝒜), (M.policy.prob θ x u *
      ∑' k, γ ^ k * ∫ y, W k y ∂(M.env.trans (x, u))) ∂μ.measure := by
      congr 1
      funext u
      exact tsum_mul_left
    _ = ∫ (u : 𝒜), (M.policy.prob θ x u *
      ∫ y, (∑' k, γ ^ k * W k y) ∂(M.env.trans (x, u))) ∂μ.measure := by
      congr 1
      funext u
      rw [hinner]


-- created on 2026-10-07
-- updated on 2026-11-14
