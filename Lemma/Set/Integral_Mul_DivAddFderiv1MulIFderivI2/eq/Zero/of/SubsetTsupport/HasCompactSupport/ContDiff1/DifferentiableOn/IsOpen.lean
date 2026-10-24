import Mathlib
import sympy.Basic
open MeasureTheory Filter Complex Metric Set
open scoped Topology


private lemma continuous_mul_of_tsupport_subset {V : Set ℂ} {f g : ℂ → ℂ} (hV : IsOpen V)
  (hf : ContinuousOn f V) (hg : Continuous g) (hgV : tsupport g ⊆ V) :
  Continuous fun z => f z * g z := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  if hz : z ∈ V then
    exact (hf.continuousAt (hV.mem_nhds hz)).mul hg.continuousAt
  else
    have hz' : z ∉ tsupport g := fun h' => hz (hgV h')
    have h0 : g =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 hz'
    have : (fun w => f w * g w) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [h0] with w hw
      simp [hw]
    exact (continuousAt_congr this).2 continuousAt_const
private lemma integrable_mul_of_tsupport_subset {V : Set ℂ} {f g : ℂ → ℂ} (hV : IsOpen V)
  (hf : ContinuousOn f V) (hg : Continuous g) (hgs : HasCompactSupport g)
  (hgV : tsupport g ⊆ V) : Integrable fun z => f z * g z :=
  (continuous_mul_of_tsupport_subset hV hf hg hgV).integrable_of_hasCompactSupport hgs.mul_left

private lemma helper_main (V : Set ℂ) (hV : IsOpen V) (G : ℂ → ℂ) (hG : DifferentiableOn ℂ G V)
  (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hV' : tsupport h ⊆ V) :
  ∫ z, G z * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = 0 := by
  have hGa : AnalyticOnNhd ℂ G V := hG.analyticOnNhd hV
  have hGcont : ContinuousOn G V := hG.continuousOn
  have hGc1 : ContDiffOn ℝ 1 G V := (hGa.contDiffOn (n := 1) hV.uniqueDiffOn).restrict_scalars ℝ
  have hdGcont : ∀ v : ℂ, ContinuousOn (fun z => fderiv ℝ G z v) V := fun v =>
    (hGc1.continuousOn_fderiv_of_isOpen hV le_rfl).clm_apply continuousOn_const
  have hhd : Differentiable ℝ h := hh.differentiable one_ne_zero
  have hdh : ∀ v : ℂ, Continuous fun z => fderiv ℝ h z v := fun v =>
    (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdh_supp : ∀ v : ℂ, HasCompactSupport fun z => fderiv ℝ h z v := fun v =>
    hsupp.fderiv_apply ℝ v
  have hdh_tsupp : ∀ v : ℂ, tsupport (fun z => fderiv ℝ h z v) ⊆ V := fun v =>
    (tsupport_fderiv_apply_subset ℝ v).trans hV'
  have hI2 : ∀ v : ℂ, Integrable fun z => G z * fderiv ℝ h z v := fun v =>
    integrable_mul_of_tsupport_subset hV hGcont (hdh v) (hdh_supp v) (hdh_tsupp v)
  have hibp : ∀ v : ℂ, ∫ z, G z * fderiv ℝ h z v = -∫ z, fderiv ℝ G z v * h z := by
    intro v
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact integrable_mul_of_tsupport_subset hV (hdGcont v) hh.continuous hsupp hV'
    · exact hI2 v
    · exact integrable_mul_of_tsupport_subset hV hGcont hh.continuous hsupp hV'
    ·
      intro x hx
      exact (hG.differentiableAt (hV.mem_nhds (hV' hx))).restrictScalars ℝ
    ·
      intro x _
      exact hhd x
  have hCR : ∀ z ∈ V, fderiv ℝ G z 1 + I * fderiv ℝ G z I = 0 := by
    intro z hz
    have hd : DifferentiableAt ℂ G z := hG.differentiableAt (hV.mem_nhds hz)
    rw [hd.hasDerivAt.complexToReal_fderiv.fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
    linear_combination deriv G z * I_mul_I
  have hA : ∫ z, fderiv ℝ G z 1 * h z = ∫ z, (-I) * (fderiv ℝ G z I * h z) := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    if hz : z ∈ tsupport h then
      have := hCR z (hV' hz)
      show fderiv ℝ G z 1 * h z = (-I) * (fderiv ℝ G z I * h z)
      linear_combination (h z) * this
    else
      simp [image_eq_zero_of_notMem_tsupport hz]
  calc
    _ = ∫ z, ((1 / 2 : ℂ) * (G z * fderiv ℝ h z 1) + (I / 2) * (G z * fderiv ℝ h z I)) := by
      congr 1
      funext z
      ring
    _ = (1 / 2 : ℂ) * (∫ z, G z * fderiv ℝ h z 1) + (I / 2) * (∫ z, G z * fderiv ℝ h z I) := by
      rw [integral_add ((hI2 1).const_mul _) ((hI2 I).const_mul _), integral_const_mul,
        integral_const_mul]
    _ = 0 := by
      rw [hibp 1, hibp I, hA, integral_const_mul]
      ring

open Complex MeasureTheory in
/--
[Complex_integral_mul_dbar_eq_zero_of_differentiableOn](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Complex_integral_mul_dbar_eq_zero_of_differentiableOn.lean)
-/
@[path]
private lemma main
  {V : Set ℂ}
  {G : ℂ → ℂ}
-- given
  (hV : IsOpen V)
  (hG : DifferentiableOn ℂ G V)
  (h : ℂ → ℂ)
  (hh : ContDiff ℝ 1 h)
  (hsupp : HasCompactSupport h)
  (hV' : tsupport h ⊆ V) :
-- imply
  ∫ z, G z * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = 0 :=
-- proof
  helper_main V hV G hG h hh hsupp hV'


-- created on 2026-10-23
