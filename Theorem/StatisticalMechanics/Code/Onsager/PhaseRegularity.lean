/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
import Def.StatisticalMechanics.Code.Onsager.PhaseRegularity


namespace StatMech.Onsager

theorem ons_hasDerivAt_gInt (beta k1 k2 : ℝ) :
    HasDerivAt (fun b => ons_gInt b k1 k2)
      (ons_gIntBetaDeriv beta k1 k2) beta := by
  have hlin : HasDerivAt (fun b : ℝ => 2 * b) 2 beta := by
    convert (hasDerivAt_id beta).const_mul 2 using 1
    all_goals ring
  have hcosh : HasDerivAt (fun b : ℝ => Real.cosh (2 * b))
      (2 * Real.sinh (2 * beta)) beta := by
    convert (Real.hasDerivAt_cosh (2 * beta)).comp beta hlin using 1
    all_goals ring
  have hsinh : HasDerivAt (fun b : ℝ => Real.sinh (2 * b))
      (2 * Real.cosh (2 * beta)) beta := by
    convert (Real.hasDerivAt_sinh (2 * beta)).comp beta hlin using 1
    all_goals ring
  have hprod := hsinh.const_mul (Real.cos k1 + Real.cos k2)
  have h := (hcosh.pow 2).sub hprod
  convert h using 1
  · ext b
    simp only [ons_gInt, Pi.pow_apply, Pi.sub_apply]
    ring
  · simp only [ons_gIntBetaDeriv]
    ring

theorem ons_hasDerivAt_gIntBetaDeriv (beta k1 k2 : ℝ) :
    HasDerivAt (fun b => ons_gIntBetaDeriv b k1 k2)
      (ons_gIntBetaDeriv2 beta k1 k2) beta := by
  have hlin : HasDerivAt (fun b : ℝ => 2 * b) 2 beta := by
    convert (hasDerivAt_id beta).const_mul 2 using 1
    all_goals ring
  have hcosh : HasDerivAt (fun b : ℝ => Real.cosh (2 * b))
      (2 * Real.sinh (2 * beta)) beta := by
    convert (Real.hasDerivAt_cosh (2 * beta)).comp beta hlin using 1
    all_goals ring
  have hsinh : HasDerivAt (fun b : ℝ => Real.sinh (2 * b))
      (2 * Real.cosh (2 * beta)) beta := by
    convert (Real.hasDerivAt_sinh (2 * beta)).comp beta hlin using 1
    all_goals ring
  have hinner : HasDerivAt
      (fun b : ℝ => 2 * Real.sinh (2 * b) - Real.cos k1 - Real.cos k2)
      (4 * Real.cosh (2 * beta)) beta := by
    convert (hsinh.const_mul 2).sub_const (Real.cos k1) |>.sub_const (Real.cos k2)
      using 1
    all_goals ring
  have h := (hcosh.const_mul 2).mul hinner
  convert h using 1
  all_goals simp only [ons_gIntBetaDeriv2]
  all_goals ring

theorem ons_hasDerivAt_log_gInt (beta k1 k2 : ℝ)
    (hne : ons_gInt beta k1 k2 ≠ 0) :
    HasDerivAt (fun b => Real.log (ons_gInt b k1 k2))
      (ons_logGIntBetaDeriv beta k1 k2) beta := by
  simpa only [ons_logGIntBetaDeriv] using
    (ons_hasDerivAt_gInt beta k1 k2).log hne

theorem ons_hasDerivAt_logGIntBetaDeriv (beta k1 k2 : ℝ)
    (hne : ons_gInt beta k1 k2 ≠ 0) :
    HasDerivAt (fun b => ons_logGIntBetaDeriv b k1 k2)
      (ons_logGIntBetaDeriv2 beta k1 k2) beta := by
  unfold ons_logGIntBetaDeriv ons_logGIntBetaDeriv2
  convert (ons_hasDerivAt_gIntBetaDeriv beta k1 k2).div
    (ons_hasDerivAt_gInt beta k1 k2) hne using 1
  all_goals simp [pow_two]

theorem ons_cosh_betaC_sq : Real.cosh (2 * ons_betaC) ^ 2 = 2 := by
  have h := Real.cosh_sq_sub_sinh_sq (2 * ons_betaC)
  rw [ons_betaC_sinh] at h
  nlinarith

theorem ons_gIntBetaDeriv_betaC (k1 k2 : ℝ) :
    ons_gIntBetaDeriv ons_betaC k1 k2 =
      2 * Real.cosh (2 * ons_betaC) * (2 - Real.cos k1 - Real.cos k2) := by
  simp only [ons_gIntBetaDeriv, ons_betaC_sinh]
  ring

theorem ons_gIntBetaDeriv2_betaC (k1 k2 : ℝ) :
    ons_gIntBetaDeriv2 ons_betaC k1 k2 =
      4 * (2 - Real.cos k1 - Real.cos k2) + 16 := by
  rw [ons_gIntBetaDeriv2, ons_betaC_sinh, ons_cosh_betaC_sq]
  ring


theorem ons_logGIntBetaDeriv_betaC (k1 k2 : ℝ)
    (hne : 2 - Real.cos k1 - Real.cos k2 ≠ 0) :
    ons_logGIntBetaDeriv ons_betaC k1 k2 = 2 * Real.cosh (2 * ons_betaC) := by
  rw [ons_logGIntBetaDeriv, ons_gIntBetaDeriv_betaC, ons_gInt_betaC]
  field_simp


theorem ons_logGIntBetaDeriv2_betaC (k1 k2 : ℝ)
    (hne : 2 - Real.cos k1 - Real.cos k2 ≠ 0) :
    ons_logGIntBetaDeriv2 ons_betaC k1 k2 =
      -4 + 16 / (2 - Real.cos k1 - Real.cos k2) := by
  rw [ons_logGIntBetaDeriv2, ons_gIntBetaDeriv2_betaC,
    ons_gIntBetaDeriv_betaC, ons_gInt_betaC]
  have hc := ons_cosh_betaC_sq
  field_simp [hne]
  rw [hc]
  ring


theorem ons_criticalDenom_le_sq (x y : ℝ) :
    2 - Real.cos x - Real.cos y ≤ (x ^ 2 + y ^ 2) / 2 := by
  have hx := Real.one_sub_sq_div_two_le_cos (x := x)
  have hy := Real.one_sub_sq_div_two_le_cos (x := y)
  linarith


theorem ons_criticalDenom_pos {x y : ℝ} (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    0 < 2 - Real.cos x - Real.cos y := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcosx : Real.cos x < 1 := by
    have h := Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by exact ⟨le_rfl, hpi.le⟩)
      (show x ∈ Set.Icc 0 Real.pi by exact ⟨hx.le, hxpi⟩) hx
    simpa using h
  have hcosy : Real.cos y ≤ 1 := Real.cos_le_one y
  linarith


theorem ons_criticalKernel_lower_on_wedge {x y : ℝ}
    (hx : 0 < x) (h2xpi : 2 * x ≤ Real.pi) (hxy : x ≤ y) (hy2x : y ≤ 2 * x) :
    2 / (5 * x ^ 2) ≤ 1 / (2 - Real.cos x - Real.cos y) := by
  have hxpi : x ≤ Real.pi := by linarith
  have hden : 0 < 2 - Real.cos x - Real.cos y :=
    ons_criticalDenom_pos hx hxpi
  have hySq : y ^ 2 ≤ 4 * x ^ 2 := by nlinarith
  have hupper : 2 - Real.cos x - Real.cos y ≤ (5 / 2 : ℝ) * x ^ 2 := by
    have hquad := ons_criticalDenom_le_sq x y
    nlinarith
  have hinv := one_div_le_one_div_of_le hden hupper
  convert hinv using 1
  field_simp


theorem ons_criticalKernel_innerIntegral_lower {x : ℝ}
    (hx : 0 < x) (h2xpi : 2 * x ≤ Real.pi) :
    2 / (5 * x) ≤
      ∫ y in x..(2 * x), 1 / (2 - Real.cos x - Real.cos y) := by
  have hx2x : x ≤ 2 * x := by linarith
  have hxpi : x ≤ Real.pi := by linarith
  have hkernelCont : ContinuousOn
      (fun y : ℝ => 1 / (2 - Real.cos x - Real.cos y)) (Set.uIcc x (2 * x)) := by
    have hdenCont : Continuous (fun y : ℝ => 2 - Real.cos x - Real.cos y) :=
      (show Continuous (fun y : ℝ => (2 - Real.cos x) - Real.cos y) from
        continuous_const.sub Real.continuous_cos)
    apply ContinuousOn.div continuousOn_const hdenCont.continuousOn
    intro y _hy
    exact (ons_criticalDenom_pos hx hxpi).ne'
  have hconstInt : IntervalIntegrable (fun _y : ℝ => 2 / (5 * x ^ 2))
      MeasureTheory.volume x (2 * x) :=
    continuousOn_const.intervalIntegrable
  have hkernelInt : IntervalIntegrable
      (fun y : ℝ => 1 / (2 - Real.cos x - Real.cos y))
      MeasureTheory.volume x (2 * x) :=
    hkernelCont.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hx2x hconstInt hkernelInt
    (fun y hy => ons_criticalKernel_lower_on_wedge hx h2xpi hy.1 hy.2)
  rw [intervalIntegral.integral_const] at hmono
  norm_num only [smul_eq_mul] at hmono
  convert hmono using 1
  field_simp
  ring


theorem ons_logKernel_integral {epsilon delta : ℝ}
    (hepsilon : 0 < epsilon) (hed : epsilon ≤ delta) :
    (∫ x in epsilon..delta, 2 / (5 * x)) =
      (2 / 5 : ℝ) * Real.log (delta / epsilon) := by
  have hzero : 0 ∉ Set.uIcc epsilon delta := by
    intro h
    rw [Set.mem_uIcc] at h
    rcases h with h | h
    · linarith
    · linarith
  calc
    (∫ x in epsilon..delta, 2 / (5 * x)) =
        ∫ x in epsilon..delta, (2 / 5 : ℝ) * x⁻¹ := by
          apply intervalIntegral.integral_congr
          intro x _hx
          field_simp
    _ = (2 / 5 : ℝ) * ∫ x in epsilon..delta, x⁻¹ :=
      intervalIntegral.integral_const_mul _ _
    _ = (2 / 5 : ℝ) * Real.log (delta / epsilon) := by
      rw [integral_inv hzero]


theorem ons_logKernel_cutoff_tendsto (delta : ℝ) (hdelta : 0 < delta) :
    Filter.Tendsto
      (fun n : ℕ => (2 / 5 : ℝ) *
        Real.log (delta / Real.exp (-(n : ℝ))))
      Filter.atTop Filter.atTop := by
  have hbase : Filter.Tendsto (fun n : ℕ => Real.log delta + (n : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
  have hmul := hbase.const_mul_atTop (by norm_num : (0 : ℝ) < 2 / 5)
  convert hmul using 1
  funext n
  rw [Real.log_div hdelta.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring


end StatMech.Onsager
