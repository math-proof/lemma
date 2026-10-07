import sympy.stats.policy_trajectory.continuous_action
import sympy.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Lemma.Random.NormRkd.le.Abs_R
import Lemma.Random.NormWkd.le.Abs_R
import Lemma.Random.MeasurableRkd
import Lemma.Random.Measurable_Wkd.of.All_Measurable_Prob
import Lemma.Random.Summable_MulPowWkd.of.In_Ico
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Real.NormIntegral.le.of.All_LeNormMul.EqIntegral_1
open MeasureTheory PolicyGradient Random Real


/--
Bellman equation of the closed-form values with continuous states and a density policy (continuous actions):
`Vkd θ γ x = ∫ u, π_θ(u | x) * Qkd θ γ x u du`.
Continuous-action counterpart of `Random.Vk.eq.Sum_MulProbQk.of.In_Ico.All_Measurable_Prob` (the action sum becomes an
integral against the reference measure of `A`); `h₀` (joint measurability of the policy) makes the integrals over the
actions and the next states meaningful, so that `∑'` and both integrals can be swapped.
-/
@[main]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {γ : ℝ}
-- given
  (h₀ : ∀ θ, Measurable (fun z : S × A => M.pol.prob θ z.1 z.2))
  (h₁ : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (x : S) :
-- imply
  M.Vkd θ γ x = ∫ u, M.pol.prob θ x u * M.Qkd θ γ x u ∂ReferenceMeasure.measure := by
-- proof
  have := M.env.trans_markov
  have hπ : Integrable (M.pol.prob θ x) ReferenceMeasure.measure :=
    Integrable.of_integral_ne_zero (by rw [M.pol.integral_eq_one θ x]; exact one_ne_zero)
  have hπm : Measurable (M.pol.prob θ x) := (h₀ θ).comp measurable_prodMk_left
  have hT : ∀ k, Measurable (fun u => ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u))) := fun k =>
    ((StronglyMeasurable.integral_kernel_prod_right' (κ := M.env.trans) (f := fun z : (S × A) × S => M.Wkd θ k z.2)
      ((Measurable_Wkd.of.All_Measurable_Prob (M := M) h₀ θ k).stronglyMeasurable.comp_measurable
        measurable_snd)).measurable).comp measurable_prodMk_left
  have hTV : Measurable (fun u => ∫ y, M.Vkd θ γ y ∂(M.env.trans (x, u))) :=
    ((StronglyMeasurable.integral_kernel_prod_right' (κ := M.env.trans) (f := fun z : (S × A) × S => M.Vkd θ γ z.2)
      ((Measurable_Vkd.of.All_Measurable_Prob (M := M) h₀ θ γ).stronglyMeasurable.comp_measurable
        measurable_snd)).measurable).comp measurable_prodMk_left
  have hb : ∀ k y, ‖γ ^ k * M.Wkd θ k y‖ ≤ γ ^ k * |M.env.R| := fun k y => by
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₁.1]
    apply mul_le_mul_of_nonneg_left (NormWkd.le.Abs_R (M := M) θ k y) (pow_nonneg h₁.1 k)
  have hI : ∀ u, HasSum (fun k => γ ^ k * ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u)))
      (∫ y, M.Vkd θ γ y ∂(M.env.trans (x, u))) := by
    intro u
    have hs : Summable fun k => ∫ y, ‖γ ^ k * M.Wkd θ k y‖ ∂(M.env.trans (x, u)) := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h₁.1 h₁.2).mul_right |M.env.R|) fun k => ?_
      have h := norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u))
        (f := fun y => ‖γ ^ k * M.Wkd θ k y‖) (C := γ ^ k * |M.env.R|)
        (Filter.Eventually.of_forall fun y => by rw [norm_norm]; exact hb k y)
      simpa using h
    have h := hasSum_integral_of_summable_integral_norm (fun k => Integrable.of_bound
      ((Measurable_Wkd.of.All_Measurable_Prob (M := M) h₀ θ k).const_mul _).aestronglyMeasurable
      (γ ^ k * |M.env.R|) (Filter.Eventually.of_forall (hb k))) hs
    simpa [integral_const_mul, DensityModel.Vkd] using h
  have hFb : ∀ k u, ‖M.pol.prob θ x u * (γ ^ k * ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u)))‖ ≤
      M.pol.prob θ x u * (γ ^ k * |M.env.R|) := fun k u => by
    have h := norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u)) (Filter.Eventually.of_forall fun y =>
      NormWkd.le.Abs_R (M := M) θ k y)
    rw [norm_mul, Real.norm_of_nonneg (M.pol.nonneg θ x u), norm_mul, norm_pow, Real.norm_of_nonneg h₁.1]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by simpa using h) (pow_nonneg h₁.1 k)) (M.pol.nonneg θ x u)
  have hFi : ∀ k, Integrable (fun u => M.pol.prob θ x u * (γ ^ k * ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u))))
      ReferenceMeasure.measure := fun k =>
    (hπ.mul_const _).mono' (hπm.mul ((hT k).const_mul _)).aestronglyMeasurable (Filter.Eventually.of_forall (hFb k))
  have hFs : Summable fun k =>
      ∫ u, ‖M.pol.prob θ x u * (γ ^ k * ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u)))‖ ∂ReferenceMeasure.measure := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h₁.1 h₁.2).mul_right |M.env.R|) fun k => ?_
    apply NormIntegral.le.of.All_LeNormMul.EqIntegral_1 (M.pol.integral_eq_one θ x)
    intro u
    rw [norm_norm]
    exact hFb k u
  have hk : ∀ k, ∫ u, M.pol.prob θ x u * (γ ^ k * ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u))) ∂ReferenceMeasure.measure =
      γ ^ k * ∫ u, M.pol.prob θ x u * ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u)) ∂ReferenceMeasure.measure := fun k => by
    rw [← integral_const_mul]
    congr 1
    funext u
    ring
  have hS : HasSum (fun k => γ ^ (k + 1) * M.Wkd θ (k + 1) x)
      (γ * ∫ u, M.pol.prob θ x u * ∫ y, M.Vkd θ γ y ∂(M.env.trans (x, u)) ∂ReferenceMeasure.measure) := by
    have h := (hasSum_integral_of_summable_integral_norm hFi hFs).mul_left γ
    have e : ∫ u, ∑' k, M.pol.prob θ x u * (γ ^ k * ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u))) ∂ReferenceMeasure.measure =
        ∫ u, M.pol.prob θ x u * ∫ y, M.Vkd θ γ y ∂(M.env.trans (x, u)) ∂ReferenceMeasure.measure := by
      congr 1
      funext u
      rw [tsum_mul_left, (hI u).tsum_eq]
    rw [e] at h
    have hf : (fun k => γ ^ (k + 1) * M.Wkd θ (k + 1) x) = fun k =>
        γ * ∫ u, M.pol.prob θ x u * (γ ^ k * ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u))) ∂ReferenceMeasure.measure := by
      funext k
      show γ ^ (k + 1) * ∫ u, M.pol.prob θ x u * ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u)) ∂ReferenceMeasure.measure = _
      rw [hk, pow_succ]
      ring
    rw [hf]
    exact h
  have hr : Integrable (fun u => M.pol.prob θ x u * M.rkd x u) ReferenceMeasure.measure :=
    (hπ.mul_const |M.env.R|).mono'
      (hπm.mul ((MeasurableRkd (M := M)).comp measurable_prodMk_left)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        rw [norm_mul, Real.norm_of_nonneg (M.pol.nonneg θ x u)]
        exact mul_le_mul_of_nonneg_left (NormRkd.le.Abs_R (M := M) x u) (M.pol.nonneg θ x u))
  have hv : Integrable (fun u => M.pol.prob θ x u * ∫ y, M.Vkd θ γ y ∂(M.env.trans (x, u))) ReferenceMeasure.measure :=
    (hπ.mul_const ((1 - γ)⁻¹ * |M.env.R|)).mono' (hπm.mul hTV).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        have h := norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u))
          (Filter.Eventually.of_forall fun y => NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₁ θ y)
        rw [norm_mul, Real.norm_of_nonneg (M.pol.nonneg θ x u)]
        exact mul_le_mul_of_nonneg_left (by simpa using h) (M.pol.nonneg θ x u))
  have e : (fun u => M.pol.prob θ x u * M.Qkd θ γ x u) =
      fun u => M.pol.prob θ x u * M.rkd x u + γ * (M.pol.prob θ x u * ∫ y, M.Vkd θ γ y ∂(M.env.trans (x, u))) :=
    funext fun u => by
      unfold DensityModel.Qkd
      ring
  rw [e, integral_add hr (hv.const_mul γ), integral_const_mul]
  show ∑' k, γ ^ k * M.Wkd θ k x = _
  rw [(Summable_MulPowWkd.of.In_Ico (M := M) h₁ θ x).tsum_eq_zero_add, hS.tsum_eq]
  show (γ ^ 0 * ∫ u, M.pol.prob θ x u * M.rkd x u ∂ReferenceMeasure.measure) + _ = _
  rw [pow_zero, one_mul]


-- created on 2026-10-07
