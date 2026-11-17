import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Lemma.Random.Summable_MulPowWkd.of.In_Ico
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory PolicyGradient Random Real
set_option maxHeartbeats 900000


/--
Bellman equation of the state value with continuous states and a density policy (continuous actions):
`V0 θ γ x = ∫ u, π_θ(u | x) * rkd x u du + γ * ∫ u, π_θ(u | x) * ∫ y, V0 θ γ y ∂T(· | x, u) du`.
The one-step reward and the expected continuation are the closed form of the action value; this identity is the
state marginal of that form and does not mention `Q0`. Continuous-action counterpart of
`Random.Vk.eq.Sum_MulProbQk.of.In_Ico.All_Measurable_Prob` (the action sum becomes an integral against the reference
measure of `𝒜`); `h₀` (joint measurability of the policy) makes the integrals over the actions and the next states
meaningful, so that `∑'` and both integrals can be swapped. Holds for every state because `V0` is the `Wkd` series.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [μ : ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
-- given
  (h₀ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.π[θ] z.1 z.2))
  (h₁ : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (sₜ : 𝒮) :
-- imply
  M.V0 θ γ sₜ =
    ∫ u, M.π[θ] sₜ u * M.rkd sₜ u ∂μ.measure +
      γ * ∫ u, M.π[θ] sₜ u * ∫ y, M.V0 θ γ y ∂(M.trans (sₜ, u)) ∂μ.measure := by
-- proof
  have hVy : ∀ y, M.V0 θ γ y = ∑' k, γ ^ k * M.Wkd θ k y := fun y => rfl
  have hπ : Integrable (M.π[θ] sₜ) ReferenceMeasure.measure :=
    Integrable.of_integral_ne_zero
      ((hStoch.integral_eq_one θ sₜ).symm ▸ one_ne_zero)
  have hπm : Measurable (M.π[θ] sₜ) := (h₀ θ).comp measurable_prodMk_left
  have hT : ∀ k, Measurable (fun u => ∫ y, M.Wkd θ k y ∂(M.trans (sₜ, u))) := fun k =>
    ((StronglyMeasurable.integral_kernel_prod_right' (κ := M.transK) (f := fun z : (𝒮 × 𝒜) × 𝒮 => M.Wkd θ k z.2)
      ((Measurable_Wkd.of.All_Measurable_Prob (M := M) h₀ θ k).stronglyMeasurable.comp_measurable
        measurable_snd)).measurable).comp measurable_prodMk_left
  have hb : ∀ k y, ‖γ ^ k * M.Wkd θ k y‖ ≤ γ ^ k * |M.R| := fun k y => by
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₁.1]
    apply mul_le_mul_of_nonneg_left (NormWkd.le.Abs_R (M := M) θ k y) (pow_nonneg h₁.1 k)
  have hI : ∀ u, HasSum (fun k => γ ^ k * ∫ y, M.Wkd θ k y ∂(M.trans (sₜ, u)))
      (∫ y, M.V0 θ γ y ∂(M.trans (sₜ, u))) := by
    intro u
    have hs : Summable fun k => ∫ y, ‖γ ^ k * M.Wkd θ k y‖ ∂(M.trans (sₜ, u)) := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h₁.1 h₁.2).mul_right |M.R|) fun k => ?_
      have h := norm_integral_le_of_norm_le_const (μ := M.trans (sₜ, u))
        (f := fun y => ‖γ ^ k * M.Wkd θ k y‖) (C := γ ^ k * |M.R|)
        (Filter.Eventually.of_forall fun y => by rw [norm_norm]; exact hb k y)
      simpa using h
    have h := hasSum_integral_of_summable_integral_norm (fun k => Integrable.of_bound
      ((Measurable_Wkd.of.All_Measurable_Prob (M := M) h₀ θ k).const_mul _).aestronglyMeasurable
      (γ ^ k * |M.R|) (Filter.Eventually.of_forall (hb k))) hs
    simpa [integral_const_mul, hVy] using h
  have hFb : ∀ k u, ‖M.π[θ] sₜ u * (γ ^ k * ∫ y, M.Wkd θ k y ∂(M.trans (sₜ, u)))‖ ≤
      M.π[θ] sₜ u * (γ ^ k * |M.R|) := fun k u => by
    have h := norm_integral_le_of_norm_le_const (μ := M.trans (sₜ, u)) (Filter.Eventually.of_forall fun y =>
      NormWkd.le.Abs_R (M := M) θ k y)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_nonneg h₁.1]
    calc
      |M.π[θ] sₜ u| * (γ ^ k * |∫ y, M.Wkd θ k y ∂(M.trans (sₜ, u))|)
          = M.π[θ] sₜ u * (γ ^ k * |∫ y, M.Wkd θ k y ∂(M.trans (sₜ, u))|) := by
        congr 1
        exact abs_of_nonneg (hStoch.nonneg θ sₜ u)
      _ ≤ M.π[θ] sₜ u * (γ ^ k * |M.R|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by simpa using h) (pow_nonneg h₁.1 k)) (hStoch.nonneg θ sₜ u)
  have hFi : ∀ k, Integrable (fun u => M.π[θ] sₜ u * (γ ^ k * ∫ y, M.Wkd θ k y ∂(M.trans (sₜ, u))))
      ReferenceMeasure.measure := fun k =>
    (hπ.mul_const _).mono' (hπm.mul ((hT k).const_mul _)).aestronglyMeasurable (Filter.Eventually.of_forall (hFb k))
  have hFs : Summable fun k =>
      ∫ u, ‖M.π[θ] sₜ u * (γ ^ k * ∫ y, M.Wkd θ k y ∂(M.trans (sₜ, u)))‖ ∂ReferenceMeasure.measure := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h₁.1 h₁.2).mul_right |M.R|) fun k => ?_
    apply NormIntegral.le.of.All_LeNormMul.EqIntegral_1 (hStoch.integral_eq_one θ sₜ)
    intro u
    rw [norm_norm]
    exact hFb k u
  have hk : ∀ k, ∫ u, M.π[θ] sₜ u * (γ ^ k * ∫ y, M.Wkd θ k y ∂(M.trans (sₜ, u))) ∂ReferenceMeasure.measure =
      γ ^ k * ∫ u, M.π[θ] sₜ u * ∫ y, M.Wkd θ k y ∂(M.trans (sₜ, u)) ∂ReferenceMeasure.measure := fun k => by
    rw [← integral_const_mul]
    congr 1
    funext u
    ring
  have hS : HasSum (fun k => γ ^ (k + 1) * M.Wkd θ (k + 1) sₜ)
      (γ * ∫ u, M.π[θ] sₜ u * ∫ y, M.V0 θ γ y ∂(M.trans (sₜ, u)) ∂ReferenceMeasure.measure) := by
    have h := (hasSum_integral_of_summable_integral_norm hFi hFs).mul_left γ
    have e : ∫ u, ∑' k, M.π[θ] sₜ u * (γ ^ k * ∫ y, M.Wkd θ k y ∂(M.trans (sₜ, u))) ∂ReferenceMeasure.measure =
        ∫ u, M.π[θ] sₜ u * ∫ y, M.V0 θ γ y ∂(M.trans (sₜ, u)) ∂ReferenceMeasure.measure := by
      congr 1
      funext u
      rw [tsum_mul_left, (hI u).tsum_eq]
    rw [e] at h
    have hf : (fun k => γ ^ (k + 1) * M.Wkd θ (k + 1) sₜ) = fun k =>
        γ * ∫ u, M.π[θ] sₜ u * (γ ^ k * ∫ y, M.Wkd θ k y ∂(M.trans (sₜ, u))) ∂ReferenceMeasure.measure := by
      funext k
      show γ ^ (k + 1) * ∫ u, M.π[θ] sₜ u * ∫ y, M.Wkd θ k y ∂(M.trans (sₜ, u)) ∂ReferenceMeasure.measure = _
      rw [hk, pow_succ]
      ring
    rw [hf]
    exact h
  rw [hVy sₜ, (Summable_MulPowWkd.of.In_Ico (M := M) h₁ θ sₜ).tsum_eq_zero_add, hS.tsum_eq, pow_zero, one_mul]
  simp [Model.Wkd]


-- created on 2026-10-07
-- updated on 2026-11-17