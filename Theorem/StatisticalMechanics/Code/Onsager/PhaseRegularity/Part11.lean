/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
import Def.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part11


namespace StatMech.Onsager

theorem ons_logGIntComplexDeriv_norm_le_noncritical {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) (k1 k2 : ℝ) :
    ‖ons_logGIntComplexDeriv z k1 k2‖ ≤
      (2 * (|Real.cosh (2 * beta)| + 1) *
          (2 * (|Real.sinh (2 * beta)| + 1) + 2)) /
        (ons_noncriticalGap beta ^ 2 / 2) := by
  have hq : ‖Complex.cos (k1 : ℂ) + Complex.cos (k2 : ℂ)‖ ≤ 2 := by
    calc
      _ ≤ ‖Complex.cos (k1 : ℂ)‖ + ‖Complex.cos (k2 : ℂ)‖ := norm_add_le _ _
      _ = |Real.cos k1| + |Real.cos k2| := by
        rw [← Complex.ofReal_cos, ← Complex.ofReal_cos]
        simp only [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 := by nlinarith [Real.abs_cos_le_one k1, Real.abs_cos_le_one k2]
  have hinner : ‖2 * Complex.sinh (2 * z) - (Real.cos k1 : ℂ) - (Real.cos k2 : ℂ)‖ ≤
      2 * (|Real.sinh (2 * beta)| + 1) + 2 := by
    calc
      _ ≤ ‖(2 : ℂ) * Complex.sinh (2 * z)‖ +
          ‖(Real.cos k1 : ℂ) + (Real.cos k2 : ℂ)‖ := by
            convert norm_sub_le ((2 : ℂ) * Complex.sinh (2 * z))
              ((Real.cos k1 : ℂ) + (Real.cos k2 : ℂ)) using 1
            all_goals ring_nf
      _ ≤ 2 * (|Real.sinh (2 * beta)| + 1) + 2 := by
        rw [norm_mul]
        norm_num
        nlinarith [hq, hz.2.2.le, norm_nonneg (Complex.sinh (2 * z))]
  have hnum : ‖ons_gIntComplexDeriv z k1 k2‖ ≤
      2 * (|Real.cosh (2 * beta)| + 1) *
        (2 * (|Real.sinh (2 * beta)| + 1) + 2) := by
    rw [ons_gIntComplexDeriv, norm_mul, norm_mul]
    norm_num
    have hinner' : ‖2 * Complex.sinh (2 * z) - Complex.cos (k1 : ℂ) -
        Complex.cos (k2 : ℂ)‖ ≤
        2 * (|Real.sinh (2 * beta)| + 1) + 2 := by
      simpa only [Complex.ofReal_cos] using hinner
    exact mul_le_mul (mul_le_mul_of_nonneg_left hz.2.1.le (by positivity))
      hinner' (norm_nonneg _) (by positivity)
  have hden := ons_gIntComplex_norm_lower_noncritical hbeta hcrit hz k1 k2
  have hgap := ons_noncriticalGap_pos hbeta hcrit
  rw [ons_logGIntComplexDeriv, norm_div]
  exact div_le_div₀ (by positivity) hnum (by positivity) hden.le

theorem ons_hasDerivAt_gIntComplex (z : ℂ) (k1 k2 : ℝ) :
    HasDerivAt (fun w => ons_gIntComplex w k1 k2)
      (ons_gIntComplexDeriv z k1 k2) z := by
  have hlin : HasDerivAt (fun w : ℂ => 2 * w) 2 z := by
    convert (hasDerivAt_id z).const_mul 2 using 1
    all_goals ring
  have hcosh : HasDerivAt (fun w : ℂ => Complex.cosh (2 * w))
      (2 * Complex.sinh (2 * z)) z := by
    convert (Complex.hasDerivAt_cosh (2 * z)).comp z hlin using 1
    all_goals ring
  have hsinh : HasDerivAt (fun w : ℂ => Complex.sinh (2 * w))
      (2 * Complex.cosh (2 * z)) z := by
    convert (Complex.hasDerivAt_sinh (2 * z)).comp z hlin using 1
    all_goals ring
  have h := (hcosh.pow 2).sub
    (hsinh.mul_const ((Real.cos k1 : ℂ) + (Real.cos k2 : ℂ)))
  convert h using 1
  unfold ons_gIntComplexDeriv
  ring

theorem ons_hasDerivAt_log_gIntComplex {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) (k1 k2 : ℝ) :
    HasDerivAt (fun w => Complex.log (ons_gIntComplex w k1 k2))
      (ons_logGIntComplexDeriv z k1 k2) z := by
  simpa only [ons_logGIntComplexDeriv] using
    (ons_hasDerivAt_gIntComplex z k1 k2).clog
      (ons_gIntComplex_mem_slitPlane_noncritical hbeta hcrit hz k1 k2)

theorem ons_complexLogGInt_continuous_momenta_noncritical {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
    Continuous (fun p : ℝ × ℝ => Complex.log (ons_gIntComplex z p.1 p.2)) := by
  have hg : Continuous (fun p : ℝ × ℝ => ons_gIntComplex z p.1 p.2) := by
    unfold ons_gIntComplex
    fun_prop
  rw [continuous_iff_continuousAt]
  intro p
  have hlog : ContinuousAt Complex.log (ons_gIntComplex z p.1 p.2) :=
    (Complex.hasDerivAt_log
      (ons_gIntComplex_mem_slitPlane_noncritical hbeta hcrit hz p.1 p.2)).continuousAt
  have hc := ContinuousAt.comp
    (f := fun q : ℝ × ℝ => ons_gIntComplex z q.1 q.2) hlog hg.continuousAt
  simpa only [Function.comp_apply] using hc

theorem ons_logGIntComplexDeriv_continuous_momenta_noncritical
    {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
    Continuous (fun p : ℝ × ℝ => ons_logGIntComplexDeriv z p.1 p.2) := by
  have hg : Continuous (fun p : ℝ × ℝ => ons_gIntComplex z p.1 p.2) := by
    unfold ons_gIntComplex
    fun_prop
  have hd : Continuous (fun p : ℝ × ℝ => ons_gIntComplexDeriv z p.1 p.2) := by
    unfold ons_gIntComplexDeriv
    fun_prop
  exact hd.div hg fun p hzero => by
    have hre := congrArg Complex.re hzero
    simp only [Complex.zero_re] at hre
    exact (ons_gIntComplex_re_pos_noncritical hbeta hcrit hz p.1 p.2).ne' hre

theorem ons_complexInnerLogIntegral_continuous_noncritical
    {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
    Continuous (fun k1 => ∫ k2 in (-Real.pi)..Real.pi,
      Complex.log (ons_gIntComplex z k1 k2)) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (ons_complexLogGInt_continuous_momenta_noncritical hbeta hcrit hz)
    (-Real.pi) Real.pi

theorem ons_complexInnerLogDerivIntegral_continuous_noncritical
    {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
    Continuous (fun k1 => ∫ k2 in (-Real.pi)..Real.pi,
      ons_logGIntComplexDeriv z k1 k2) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (ons_logGIntComplexDeriv_continuous_momenta_noncritical hbeta hcrit hz)
    (-Real.pi) Real.pi

theorem ons_hasDerivAt_complexInnerIntegral_noncritical
    {beta : ℝ} {z : ℂ} (k1 : ℝ)
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
    HasDerivAt
      (fun w => ∫ k2 in (-Real.pi)..Real.pi,
        Complex.log (ons_gIntComplex w k1 k2))
      (∫ k2 in (-Real.pi)..Real.pi,
        ons_logGIntComplexDeriv z k1 k2) z := by
  let C : ℝ :=
    (2 * (|Real.cosh (2 * beta)| + 1) *
        (2 * (|Real.sinh (2 * beta)| + 1) + 2)) /
      (ons_noncriticalGap beta ^ 2 / 2)
  have hs : ons_complexNoncriticalNeighborhood beta ∈ nhds z :=
    (ons_complexNoncriticalNeighborhood_isOpen beta).mem_nhds hz
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w k2 => Complex.log (ons_gIntComplex w k1 k2))
    (F' := fun w k2 => ons_logGIntComplexDeriv w k1 k2)
    (bound := fun _ => C) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with w hw
    exact ((ons_complexLogGInt_continuous_momenta_noncritical hbeta hcrit hw).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ((ons_complexLogGInt_continuous_momenta_noncritical hbeta hcrit hz).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact ((ons_logGIntComplexDeriv_continuous_momenta_noncritical hbeta hcrit hz).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [] with k2 _hk2 w hw
    simpa only [C] using
      ons_logGIntComplexDeriv_norm_le_noncritical hbeta hcrit hw k1 k2
  · exact intervalIntegral.intervalIntegrable_const
  · filter_upwards [] with k2 _hk2 w hw
    exact ons_hasDerivAt_log_gIntComplex hbeta hcrit hw k1 k2

theorem ons_hasDerivAt_complexDoubleIntegral_noncritical
    {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
    HasDerivAt
      (fun w => ∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi,
          Complex.log (ons_gIntComplex w k1 k2))
      (∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi,
          ons_logGIntComplexDeriv z k1 k2) z := by
  let C : ℝ :=
    (2 * (|Real.cosh (2 * beta)| + 1) *
        (2 * (|Real.sinh (2 * beta)| + 1) + 2)) /
      (ons_noncriticalGap beta ^ 2 / 2)
  let B : ℝ := C * (2 * Real.pi)
  have hs : ons_complexNoncriticalNeighborhood beta ∈ nhds z :=
    (ons_complexNoncriticalNeighborhood_isOpen beta).mem_nhds hz
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w k1 => ∫ k2 in (-Real.pi)..Real.pi,
      Complex.log (ons_gIntComplex w k1 k2))
    (F' := fun w k1 => ∫ k2 in (-Real.pi)..Real.pi,
      ons_logGIntComplexDeriv w k1 k2)
    (bound := fun _ => B) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with w hw
    exact (ons_complexInnerLogIntegral_continuous_noncritical
      hbeta hcrit hw).aestronglyMeasurable
  · exact (ons_complexInnerLogIntegral_continuous_noncritical hbeta hcrit hz).intervalIntegrable _ _
  · exact (ons_complexInnerLogDerivIntegral_continuous_noncritical
      hbeta hcrit hz).aestronglyMeasurable
  · filter_upwards [] with k1 _hk1 w hw
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -Real.pi) (b := Real.pi)
      (f := fun k2 => ons_logGIntComplexDeriv w k1 k2) (C := C)
      (fun (k2 : ℝ) _hk2 => by
        simpa only [C] using
          ons_logGIntComplexDeriv_norm_le_noncritical hbeta hcrit hw k1 k2)
    calc
      ‖∫ k2 in (-Real.pi)..Real.pi,
          ons_logGIntComplexDeriv w k1 k2‖ ≤
          C * |Real.pi - (-Real.pi)| := hbound
      _ = B := by
        rw [abs_of_pos (show 0 < Real.pi - (-Real.pi) by
          linarith [Real.pi_pos])]
        simp only [B]
        ring
  · exact intervalIntegral.intervalIntegrable_const
  · filter_upwards [] with k1 _hk1 w hw
    exact ons_hasDerivAt_complexInnerIntegral_noncritical k1 hbeta hcrit hw

end StatMech.Onsager
