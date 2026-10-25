import Mathlib
import sympy.Basic
import Instance.Analysis.SpecialFunctions.ExponentialIntegral.E1.PrincipalIntegral
open Filter Set Topology MeasureTheory
open scoped ENNReal NNReal
open Complex


/--
[measurable_expPosDensity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/PrincipalIntegral.lean)
-/
@[path]
private lemma measurable_expPosDensity : Measurable expPosDensity := by
  unfold expPosDensity
  apply Measurable.ennreal_ofReal
  unfold expPosWeight
  exact Measurable.ite measurableSet_Ioi
    (Real.continuous_exp.comp continuous_neg).measurable measurable_const

/--
[integrable_expPosWeight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/PrincipalIntegral.lean)
-/
@[path]
private lemma integrable_expPosWeight : Integrable expPosWeight := by
  have h := integrableOn_exp_neg_Ioi 0
  have hi := h.integrable_indicator measurableSet_Ioi
  rw [show expPosWeight = (Ioi 0).indicator (fun t : ℝ => Real.exp (-t)) by
    funext t
    simp [expPosWeight, Set.indicator]]
  convert hi using 1

/--
[support_expPosMeasure_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/PrincipalIntegral.lean)
-/
@[path]
private lemma support_expPosMeasure_subset : expPosMeasure.support ⊆ Ici 0 := by
  apply Measure.support_subset_of_isClosed isClosed_Ici
  change ∀ᵐ t ∂expPosMeasure, t ∈ Ici 0
  rw [expPosMeasure, ae_withDensity_iff measurable_expPosDensity]
  filter_upwards with t
  intro ht
  by_cases h : 0 < t
  · exact h.le
  · exfalso
    apply ht
    simp [expPosDensity, expPosWeight, h]

/--
[resolventTransform_neg_eq_kernel](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/PrincipalIntegral.lean)
-/
@[path]
private lemma resolventTransform_neg_eq_kernel (z : ℂ) :
  resolventTransform expPosMeasure (-z) =
    ∫ t : ℝ in Ioi 0, (Real.exp (-t) : ℂ) / ((t : ℂ) + z) := by
  rw [resolventTransform_apply, expPosMeasure,
    integral_withDensity_eq_integral_toReal_smul measurable_expPosDensity
      (Filter.Eventually.of_forall (fun _ => by simp [expPosDensity]))]
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with t
  simp only [expPosDensity, expPosWeight]
  by_cases ht : 0 < t
  · simp only [ht, ite_eq_left, mem_Ioi, indicator_of_mem,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
    rw [resolvent, sub_neg_eq_add]
    simp [div_eq_mul_inv, mul_comm]
  · simp [Set.indicator, ht]

namespace Complex

/--
[neg_notMem_expPosSupport_image](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/PrincipalIntegral.lean)
-/
@[path]
private lemma neg_notMem_expPosSupport_image {z : ℂ} (hz : z ∈ Complex.slitPlane) :
  -z ∉ (algebraMap ℝ ℂ) '' expPosMeasure.support := by
  rintro ⟨t, ht, htz⟩
  have ht0 : 0 ≤ t := support_expPosMeasure_subset ht
  rw [Complex.mem_slitPlane_iff] at hz
  obtain hzre | hzim := hz
  · have hre := congrArg Complex.re htz
    change t = -z.re at hre
    linarith
  · have him := congrArg Complex.im htz
    change 0 = -z.im at him
    exact hzim (by linarith)

end Complex

namespace Complex

/--
[differentiableOn_principalE1Raw](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/PrincipalIntegral.lean)
-/
@[path]
private lemma differentiableOn_principalE1Raw :
  DifferentiableOn ℂ principalExponentialIntegralE1Raw Complex.slitPlane := by
  intro z hz
  exact (((differentiable_ein z).sub
    (Complex.hasDerivAt_log hz).differentiableAt).sub
      (differentiableAt_const (c := (Real.eulerMascheroniConstant : ℂ)))).differentiableWithinAt

end Complex

namespace Complex

/--
[differentiableOn_kernelModel](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/PrincipalIntegral.lean)
-/
@[path]
private lemma differentiableOn_kernelModel :
  DifferentiableOn ℂ
    (fun z : ℂ => Complex.exp (-z) * resolventTransform expPosMeasure (-z))
    Complex.slitPlane := by
  intro z hz
  have hneg : HasDerivAt (fun w : ℂ => -w) (-1) z := (hasDerivAt_id z).neg
  have hres := (hasDerivAt_resolventTransform (-z)
    (neg_notMem_expPosSupport_image hz)).comp z hneg
  have hexp := (Complex.hasDerivAt_exp (-z)).comp z hneg
  exact (hexp.mul hres).differentiableAt.differentiableWithinAt

end Complex

namespace Complex

/--
[principal_e1_integral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/PrincipalIntegral.lean)
-/
@[path]
lemma principal_e1_integral
  {z : ℂ}
-- given
  (hz : z ≠ 0)
  (harg : |z.arg| < Real.pi) :
-- imply
  principalExponentialIntegralE1 z hz =
    Complex.exp (-z) *
    ∫ t : ℝ in Ioi 0, (Real.exp (-t) : ℂ) / ((t : ℂ) + z) := by
-- proof
  let Q : ℂ → ℂ := fun w =>
    Complex.exp (-w) * resolventTransform expPosMeasure (-w)
  have hzslit : z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff_arg]
    refine ⟨?_, hz⟩
    intro h
    rwa [h, abs_of_nonneg Real.pi_nonneg] at harg
  have hP : AnalyticOnNhd ℂ principalExponentialIntegralE1Raw Complex.slitPlane :=
    differentiableOn_principalE1Raw.analyticOnNhd Complex.isOpen_slitPlane
  have hQ : AnalyticOnNhd ℂ Q Complex.slitPlane := by
    apply DifferentiableOn.analyticOnNhd _ Complex.isOpen_slitPlane
    simpa only [Q] using differentiableOn_kernelModel
  have hevent : ∀ᶠ x : ℝ in 𝓝[≠] (1 : ℝ),
    principalExponentialIntegralE1Raw (x : ℂ) = Q (x : ℂ) := by
    filter_upwards
      [(eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left]
      with x hx
    dsimp only [Q]
    rw [resolventTransform_neg_eq_kernel]
    simpa only [principalExponentialIntegralE1_eq_raw] using
      euler_constant_normalization x hx
  have hfreq := hevent.frequently
  have hmap : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 1) (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact tendsto_nhdsWithin_of_tendsto_nhds Complex.continuous_ofReal.continuousAt
    · exact eventually_nhdsWithin_iff.mpr
      (Eventually.of_forall fun t ht => Complex.ofReal_ne_one.mpr ht)
  have hfreqC : ∃ᶠ w : ℂ in 𝓝[≠] 1,
    principalExponentialIntegralE1Raw w = Q w := hmap.frequently hfreq
  have heq := hP.eqOn_of_preconnected_of_frequently_eq hQ
    (Complex.starConvex_one_slitPlane.isPathConnected
      Complex.one_mem_slitPlane).isConnected.isPreconnected
    Complex.one_mem_slitPlane hfreqC
  dsimp only [Q] at heq
  rw [principalExponentialIntegralE1_eq_raw]
  rw [heq hzslit]
  change Complex.exp (-z) * resolventTransform expPosMeasure (-z) = _
  rw [resolventTransform_neg_eq_kernel]

end Complex


-- created on 2026-10-20
-- updated on 2026-10-23
