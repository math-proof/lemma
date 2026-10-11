import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# A regularized-integral formula for the Euler-Mascheroni constant

This file expresses the Euler-Mascheroni constant as the difference of two convergent
integrals obtained by splitting and regularizing the logarithmic Gamma integral at one.
-/

open Filter Set Topology MeasureTheory Asymptotics Real

noncomputable section

namespace Real

private theorem integral_exp_neg_mul_log_eq_neg_euler :
    (∫ t : ℝ in Ioi 0, (Real.exp (-t) * Real.log t : ℂ)) =
      -(Real.eulerMascheroniConstant : ℂ) := by
  have hGI := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)
  have hEq : Complex.Gamma =ᶠ[𝓝 (1 : ℂ)] Complex.GammaIntegral := by
    have hopen : IsOpen {s : ℂ | 0 < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℂ) ∈ {s : ℂ | 0 < s.re})]
      with s hs
    exact Complex.Gamma_eq_integral hs
  have hd : deriv Complex.Gamma (1 : ℂ) =
      ∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((1 : ℂ) - 1) *
        (Real.log t * Real.exp (-t)) := by
    rw [hEq.deriv_eq, hGI.deriv]
  rw [Complex.hasDerivAt_Gamma_one.deriv] at hd
  simpa [mul_comm] using hd.symm

private theorem integrableOn_exp_neg_mul_log :
    IntegrableOn (fun t : ℝ => (Real.exp (-t) * Real.log t : ℂ)) (Ioi 0) := by
  have hm :=
    (mellin_hasDerivAt_of_isBigO_rpow (E := ℂ) (a := 2) (b := 0)
      (f := fun x : ℝ => (Real.exp (-x) : ℂ)) (s := (1 : ℂ))
      (by
        refine (Continuous.continuousOn ?_).locallyIntegrableOn measurableSet_Ioi
        exact Complex.continuous_ofReal.comp
          (Real.continuous_exp.comp continuous_neg))
      (by
        rw [← isBigO_norm_left]
        simp_rw [Complex.norm_real, isBigO_norm_left]
        simpa only [neg_one_mul] using
          (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one _).isBigO)
      (by norm_num)
      (by
        simp_rw [neg_zero, rpow_zero]
        refine isBigO_const_of_tendsto
          (?_ : Tendsto (fun x : ℝ => (Real.exp (-x) : ℂ)) (𝓝[>] 0) (𝓝 1)) one_ne_zero
        rw [(by simp : (1 : ℂ) = Real.exp (-0))]
        exact (Complex.continuous_ofReal.comp
          (Real.continuous_exp.comp continuous_neg)).continuousWithinAt)
      (by norm_num)).1
  simpa only [MellinConvergent, sub_self, Complex.cpow_zero, one_smul,
    Complex.real_smul, one_mul, mul_comm] using hm

private theorem tendsto_exp_neg_sub_one_div_zero :
    Tendsto (fun t : ℝ => (Real.exp (-t) - 1) / t) (𝓝[>] 0) (𝓝 (-1)) := by
  have hd : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-1) 0 := by
    convert ((hasDerivAt_id (𝕜 := ℝ) 0).neg.exp) using 1 <;> norm_num
  simpa [div_eq_inv_mul, mul_comm] using hd.tendsto_slope_zero_right

theorem intervalIntegrable_exp_neg_sub_one_div :
    IntervalIntegrable
      (fun t : ℝ => (((Real.exp (-t) - 1) / t : ℝ) : ℂ)) volume 0 1 := by
  let q : ℝ → ℝ := fun t => (Real.exp (-t) - 1) / t
  let q0 : ℝ → ℝ := Function.update q 0 (-1)
  have hq : Tendsto q (𝓝[>] 0) (𝓝 (-1)) := by
    simpa only [q] using tendsto_exp_neg_sub_one_div_zero
  have hq0 : ContinuousOn q0 (Icc 0 1) := by
    change ContinuousOn (Function.update q 0 (-1)) (Icc 0 1)
    rw [continuousOn_update_iff]
    constructor
    · apply ContinuousOn.div
      · exact (Real.continuous_exp.comp continuous_neg).continuousOn.sub continuousOn_const
      · exact continuousOn_id
      · intro x hx
        exact hx.2
    · intro _
      exact hq.mono_left (nhdsWithin_mono 0 (by
        intro x hx
        exact lt_of_le_of_ne hx.1.1 (Ne.symm hx.2)))
  have hq0comp : ContinuousOn (fun t : ℝ => (q0 t : ℂ)) (Icc 0 1) := by
    change ContinuousOn (Complex.ofReal ∘ q0) (Icc 0 1)
    exact Complex.continuous_ofReal.comp_continuousOn hq0
  have hq0int : IntervalIntegrable (fun t : ℝ => (q0 t : ℂ)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using hq0comp
  apply hq0int.congr_uIoo
  intro x hx
  rw [uIoo_of_le zero_le_one] at hx
  change (Function.update q 0 (-1) x : ℂ) = _
  rw [Function.update_of_ne hx.1.ne']

private theorem integrableOn_exp_neg_div_Ioi_one :
    IntegrableOn (fun t : ℝ => ((Real.exp (-t) / t : ℝ) : ℂ)) (Ioi 1) := by
  have he : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 1) :=
    integrableOn_exp_neg_Ioi 1
  have hr : IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Ioi 1) := by
    refine he.mono' ?_ ?_
    · exact ((Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
          (fun x hx => (zero_lt_one.trans hx).ne')).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := zero_lt_one.trans hx
      simpa [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos hx0] using
        (div_le_self (Real.exp_pos (-x)).le hx.le)
  exact hr.ofReal

private theorem integral_exp_neg_mul_log_zero_one :
    (∫ t : ℝ in 0..1, Real.exp (-t) * Real.log t) =
      ∫ t : ℝ in 0..1, (Real.exp (-t) - 1) / t := by
  let h : ℝ → ℝ := fun t => Real.exp (-t) * Real.log t
  let q : ℝ → ℝ := fun t => (Real.exp (-t) - 1) / t
  let F0 : ℝ → ℝ := fun t => (Real.exp (-t) - 1) * Real.log t
  have hh : IntervalIntegrable h volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have hc := integrableOn_exp_neg_mul_log.mono_set
      (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 1 ⊆ Ioi 0)
    have hr := Complex.reCLM.integrable_comp hc
    change Integrable h (volume.restrict (Ioc 0 1))
    simpa only [Function.comp_apply, Complex.reCLM_apply, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, add_zero, h] using hr
  have hq : IntervalIntegrable q volume 0 1 := by
    have hc := intervalIntegrable_exp_neg_sub_one_div
    rw [intervalIntegrable_iff] at hc ⊢
    have hr := Complex.reCLM.integrable_comp hc
    change Integrable q (volume.restrict (uIoc 0 1))
    simpa only [Function.comp_apply, Complex.reCLM_apply, Complex.ofReal_re, q] using hr
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F0 (-h x + q x) x := by
    intro x hx
    dsimp only [F0, h, q]
    have hd := (((hasDerivAt_neg x).exp.sub_const 1).mul
      (Real.hasDerivAt_log hx.1.ne'))
    apply hd.congr_deriv
    field_simp [hx.1.ne']
  have hF0_zero : Tendsto F0 (𝓝[>] 0) (𝓝 0) := by
    have hq0 : Tendsto q (𝓝[>] 0) (𝓝 (-1)) := by
      simpa only [q] using tendsto_exp_neg_sub_one_div_zero
    have htlog : Tendsto (fun t : ℝ => t * Real.log t) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Real.rpow_one, mul_comm] using
        tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
    have hp := hq0.mul htlog
    have heq : F0 =ᶠ[𝓝[>] 0] fun t => q t * (t * Real.log t) := by
      filter_upwards [eventually_mem_nhdsWithin] with t ht
      dsimp only [F0, q]
      field_simp [(show 0 < t from ht).ne']
    simpa only [mul_zero] using hp.congr' heq.symm
  have hF0_one : Tendsto F0 (𝓝[<] 1) (𝓝 0) := by
    have hc : ContinuousAt F0 1 := by
      dsimp only [F0]
      exact ((Real.continuous_exp.comp continuous_neg).continuousAt.sub continuousAt_const).mul
        (continuousAt_log one_ne_zero)
    have ht := hc.tendsto.mono_left
      (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from inf_le_left)
    simpa [F0] using ht
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := F0) (f' := fun x => -h x + q x) (fa := 0) (fb := 0)
    (by norm_num : (0 : ℝ) < 1) hderiv (hh.neg.add hq) hF0_zero hF0_one
  change (∫ y : ℝ in 0..1, (-h) y + q y) = 0 - 0 at hFTC
  rw [intervalIntegral.integral_add hh.neg hq] at hFTC
  change (∫ x : ℝ in 0..1, -h x) + (∫ x : ℝ in 0..1, q x) = 0 - 0 at hFTC
  rw [intervalIntegral.integral_neg] at hFTC
  dsimp only [h, q] at hFTC ⊢
  linarith

private theorem integral_exp_neg_mul_log_Ioi_one :
    (∫ t : ℝ in Ioi 1, Real.exp (-t) * Real.log t) =
      ∫ t : ℝ in Ioi 1, Real.exp (-t) / t := by
  let h : ℝ → ℝ := fun t => Real.exp (-t) * Real.log t
  let r : ℝ → ℝ := fun t => Real.exp (-t) / t
  let Finf : ℝ → ℝ := fun t => -Real.exp (-t) * Real.log t
  have hh : IntegrableOn h (Ioi 1) := by
    have hc := integrableOn_exp_neg_mul_log.mono_set
      (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))
    have hr := Complex.reCLM.integrable_comp hc
    change Integrable h (volume.restrict (Ioi 1))
    simpa only [Function.comp_apply, Complex.reCLM_apply, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, add_zero, h] using hr
  have hr : IntegrableOn r (Ioi 1) := by
    have hc := integrableOn_exp_neg_div_Ioi_one
    have hr' := Complex.reCLM.integrable_comp hc
    change Integrable r (volume.restrict (Ioi 1))
    simpa only [Function.comp_apply, Complex.reCLM_apply, Complex.ofReal_re, r] using hr'
  have hderiv : ∀ x ∈ Ioi (1 : ℝ), HasDerivAt Finf (h x - r x) x := by
    intro x hx
    have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
    dsimp only [Finf, h, r]
    have hd := ((hasDerivAt_neg x).exp.neg.mul (Real.hasDerivAt_log hx0))
    apply hd.congr_deriv
    field_simp [hx0]
    simp only [Pi.neg_apply]
    ring
  have hcont : ContinuousWithinAt Finf (Ici 1) 1 := by
    apply ContinuousAt.continuousWithinAt
    dsimp only [Finf]
    exact ((Real.continuous_exp.comp continuous_neg).continuousAt.neg.mul
      (continuousAt_log one_ne_zero))
  have hlim : Tendsto Finf atTop (𝓝 0) := by
    have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
      simpa only [Real.rpow_one] using
        (isLittleO_log_rpow_atTop one_pos).tendsto_div_nhds_zero
    have hpow := tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have hp := hlog.mul hpow
    have heq : Finf =ᶠ[atTop]
        fun t => -((Real.log t / t) * (t ^ 1 * Real.exp (-t))) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      dsimp only [Finf]
      field_simp [ht.ne']
    simpa only [zero_mul, neg_zero] using hp.neg.congr' heq.symm
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := Finf) (f' := fun x => h x - r x) (m := 0)
    hcont hderiv (hh.sub hr) hlim
  rw [integral_sub hh hr] at hFTC
  dsimp only [Finf, h, r] at hFTC ⊢
  simp only [Real.log_one, mul_zero, sub_zero] at hFTC
  linarith

theorem eulerMascheroniConstant_eq_regularized_integrals :
    (Real.eulerMascheroniConstant : ℂ) =
      (∫ t : ℝ in 0..1, (((1 - Real.exp (-t)) / t : ℝ) : ℂ)) -
        ∫ t : ℝ in Ioi 1, ((Real.exp (-t) / t : ℝ) : ℂ) := by
  let hC : ℝ → ℂ := fun t => ((Real.exp (-t) * Real.log t : ℝ) : ℂ)
  let qC : ℝ → ℂ := fun t => (((Real.exp (-t) - 1) / t : ℝ) : ℂ)
  let aC : ℝ → ℂ := fun t => (((1 - Real.exp (-t)) / t : ℝ) : ℂ)
  let rC : ℝ → ℂ := fun t => ((Real.exp (-t) / t : ℝ) : ℂ)
  have h0 : IntegrableOn hC (Ioi 0) := by
    simpa only [hC, Complex.ofReal_mul] using integrableOn_exp_neg_mul_log
  have h1 : IntegrableOn hC (Ioi 1) :=
    h0.mono_set (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (f := hC) (a := 0) (b := 1) h0 h1
  have hgamma : (∫ t : ℝ in Ioi 0, hC t) =
      -(Real.eulerMascheroniConstant : ℂ) := by
    simpa only [hC, Complex.ofReal_mul] using integral_exp_neg_mul_log_eq_neg_euler
  have hlower : (∫ t : ℝ in 0..1, hC t) = ∫ t : ℝ in 0..1, qC t := by
    rw [show (∫ t : ℝ in 0..1, hC t) =
        Complex.ofReal (∫ t : ℝ in 0..1, Real.exp (-t) * Real.log t) by
          simpa only [hC] using
            (intervalIntegral.integral_ofReal
              (f := fun t : ℝ => Real.exp (-t) * Real.log t)),
      show (∫ t : ℝ in 0..1, qC t) =
        Complex.ofReal (∫ t : ℝ in 0..1, (Real.exp (-t) - 1) / t) by
          simpa only [qC] using
            (intervalIntegral.integral_ofReal
              (f := fun t : ℝ => (Real.exp (-t) - 1) / t)),
      integral_exp_neg_mul_log_zero_one]
  have hupper : (∫ t : ℝ in Ioi 1, hC t) = ∫ t : ℝ in Ioi 1, rC t := by
    rw [show (∫ t : ℝ in Ioi 1, hC t) =
        Complex.ofReal (∫ t : ℝ in Ioi 1, Real.exp (-t) * Real.log t) by
          simpa only [hC] using
            (integral_complex_ofReal
              (f := fun t : ℝ => Real.exp (-t) * Real.log t)
              (μ := volume.restrict (Ioi 1))),
      show (∫ t : ℝ in Ioi 1, rC t) =
        Complex.ofReal (∫ t : ℝ in Ioi 1, Real.exp (-t) / t) by
          simpa only [rC] using
            (integral_complex_ofReal
              (f := fun t : ℝ => Real.exp (-t) / t)
              (μ := volume.restrict (Ioi 1))),
      integral_exp_neg_mul_log_Ioi_one]
  have hqa : qC = fun t => -aC t := by
    funext t
    dsimp only [qC, aC]
    rw [← Complex.ofReal_neg]
    congr 1
    ring
  rw [hlower, hqa, intervalIntegral.integral_neg, hupper, hgamma] at hsplit
  dsimp only [aC, rC] at hsplit ⊢
  linear_combination hsplit

end Real

end
