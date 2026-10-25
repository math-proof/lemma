/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricJacobian.Part3
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootDensityKernel.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexRootDensityContractionRate_mem_Ico
    {c : Real} (hc : 2 < c) :
    sixVertexRootDensityContractionRate c ∈ Set.Ico 0 1 := by
  let d := sixVertexAnisotropyMagnitude c
  let s := sixVertexRootDensityScale c
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hs : 0 < s := sixVertexRootDensityScale_pos hc
  have hfloor : 0 < sixVertexRootDensityKernelFloor c :=
    sixVertexRootDensityKernelFloor_pos hc
  have hden : 0 < d + 1 := by linarith
  have hmargin : 0 < sixVertexRootDensityKernelFloor c * s / (d + 1) :=
    div_pos (mul_pos hfloor hs) hden
  have hmargin_le :
      sixVertexRootDensityKernelFloor c * s / (d + 1) ≤ 1 := by
    dsimp [sixVertexRootDensityKernelFloor]
    rw [div_mul_eq_mul_div, div_div]
    rw [div_le_one (mul_pos (mul_pos hs (by positivity)) hden)]
    have hd0 : 0 ≤ d := le_trans (by norm_num) hd.le
    nlinarith [sq_nonneg (d - 1), sq_nonneg (d + 1)]
  dsimp [sixVertexRootDensityContractionRate]
  constructor <;> linarith

theorem sixVertexRootDensity_reciprocalWeight_lower
    {c : Real} (hc : 2 < c) (y : Real) :
    sixVertexRootDensityScale c /
        (sixVertexAnisotropyMagnitude c + 1) ≤
      1 / sixVertexRootDensityWeight c y := by
  let d := sixVertexAnisotropyMagnitude c
  let s := sixVertexRootDensityScale c
  let Fy := sixVertexBetheIntegratingFactor c y
  have hs : 0 < s := sixVertexRootDensityScale_pos hc
  have hFy : 0 < Fy := sixVertexBetheIntegratingFactor_pos hc y
  have hupper : Fy ≤ d + 1 := (sixVertexBetheIntegratingFactor_bounds hc y).2
  have hquot : s / (d + 1) ≤ s / Fy :=
    div_le_div_of_nonneg_left hs.le hFy hupper
  change s / (d + 1) ≤ 1 / (Fy / s)
  rw [one_div_div]
  exact hquot

theorem intervalIntegral_one_div_sixVertexRootDensityWeight_lower
    {c : Real} (hc : 2 < c) :
    2 * Real.pi *
        (sixVertexRootDensityScale c /
          (sixVertexAnisotropyMagnitude c + 1)) ≤
      ∫ y in -Real.pi..Real.pi, 1 / sixVertexRootDensityWeight c y := by
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  let a := sixVertexRootDensityScale c /
    (sixVertexAnisotropyMagnitude c + 1)
  have hconst : IntervalIntegrable (fun _ : Real => a)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    continuous_const.intervalIntegrable _ _
  have hrecip : IntervalIntegrable
      (fun y : Real => 1 / sixVertexRootDensityWeight c y)
      MeasureTheory.volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    apply Continuous.div continuous_const
    · unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
        sixVertexRootDensityScale
      fun_prop
    · intro y
      exact (sixVertexRootDensityWeight_pos hc y).ne'
  have hmono := intervalIntegral.integral_mono_on hab hconst hrecip
    (fun y _ => sixVertexRootDensity_reciprocalWeight_lower hc y)
  have hconstEval :
      (∫ _y in -Real.pi..Real.pi, a) = 2 * Real.pi * a := by
    simp [a]
    ring
  rw [hconstEval] at hmono
  exact hmono


theorem sixVertexRootDensityKernel_contraction
    {c : Real} (hc : 2 < c) {e : Real → Real} {E : Real}
    (he : Continuous e) (hE : 0 ≤ E)
    (hmass : (∫ y in -Real.pi..Real.pi,
      e y / sixVertexRootDensityWeight c y) = 0)
    (hbound : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |e y| ≤ E)
    (x : Real) :
    |(1 / (2 * Real.pi)) *
        ∫ y in -Real.pi..Real.pi,
          (sixVertexRootDensityKernel c x y /
            sixVertexRootDensityWeight c y) * e y| ≤
      sixVertexRootDensityContractionRate c * E := by
  let floor := sixVertexRootDensityKernelFloor c
  let rate := sixVertexRootDensityContractionRate c
  let H : Real → Real := fun y =>
    (sixVertexRootDensityKernel c x y - floor) /
      sixVertexRootDensityWeight c y
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hfloor : 0 < floor := sixVertexRootDensityKernelFloor_pos hc
  have hHnonneg (y : Real) : 0 ≤ H y := by
    exact div_nonneg
      (sub_nonneg.mpr (sixVertexRootDensityKernelFloor_le hc x y))
      (sixVertexRootDensityWeight_pos hc y).le
  have hweightCont : Continuous (sixVertexRootDensityWeight c) := by
    unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
      sixVertexRootDensityScale
    fun_prop
  have hinvWeightCont : Continuous
      (fun y : Real => 1 / sixVertexRootDensityWeight c y) := by
    apply Continuous.div continuous_const hweightCont
    intro y
    exact (sixVertexRootDensityWeight_pos hc y).ne'
  have hkernelCont : Continuous (sixVertexRootDensityKernel c x) := by
    unfold sixVertexRootDensityKernel sixVertexRootDensityScale
      sixVertexBetheIntegratingFactor sixVertexThetaDerivativeDenominator
      sixVertexThetaDenominator sixVertexAnisotropyMagnitude sixVertexDelta
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro y
      exact (mul_pos (sixVertexRootDensityScale_pos hc)
        (sixVertexThetaDerivativeDenominator_pos hc x y)).ne'
  have hkernelQuotCont : Continuous (fun y : Real =>
      sixVertexRootDensityKernel c x y /
        sixVertexRootDensityWeight c y) :=
    hkernelCont.div hweightCont
      (fun y => (sixVertexRootDensityWeight_pos hc y).ne')
  have hfloorInvCont : Continuous (fun y : Real =>
      floor * (1 / sixVertexRootDensityWeight c y)) :=
    continuous_const.mul hinvWeightCont
  have hHcont : Continuous H := by
    apply Continuous.div
    · exact hkernelCont.sub continuous_const
    · exact hweightCont
    · intro y
      exact (sixVertexRootDensityWeight_pos hc y).ne'
  have hfloorTermCont : Continuous (fun y : Real =>
      (floor / sixVertexRootDensityWeight c y) * e y) := by
    exact (continuous_const.div hweightCont
      (fun y => (sixVertexRootDensityWeight_pos hc y).ne')).mul he
  have hHeq :
      (∫ y in -Real.pi..Real.pi,
        (sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y) * e y) =
      ∫ y in -Real.pi..Real.pi, H y * e y := by
    have hzero :
        (∫ y in -Real.pi..Real.pi,
          (floor / sixVertexRootDensityWeight c y) * e y) = 0 := by
      have hfactor : (fun y : Real =>
          (floor / sixVertexRootDensityWeight c y) * e y) =
          fun y => floor * (e y / sixVertexRootDensityWeight c y) := by
        funext y
        ring
      rw [hfactor, intervalIntegral.integral_const_mul, hmass, mul_zero]
    rw [show (fun y : Real =>
        (sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y) * e y) =
        fun y => H y * e y +
          (floor / sixVertexRootDensityWeight c y) * e y by
      funext y
      dsimp [H]
      ring]
    have hadd := intervalIntegral.integral_add (μ := MeasureTheory.volume)
      ((hHcont.mul he).intervalIntegrable (-Real.pi) Real.pi)
      (hfloorTermCont.intervalIntegrable (-Real.pi) Real.pi)
    change (∫ y in -Real.pi..Real.pi,
        H y * e y + (floor / sixVertexRootDensityWeight c y) * e y) =
      (∫ y in -Real.pi..Real.pi, H y * e y) +
        ∫ y in -Real.pi..Real.pi,
          (floor / sixVertexRootDensityWeight c y) * e y at hadd
    rw [hadd, hzero, add_zero]
  have habsolute :
      |∫ y in -Real.pi..Real.pi, H y * e y| ≤
        ∫ y in -Real.pi..Real.pi, H y * |e y| := by
    calc
      |∫ y in -Real.pi..Real.pi, H y * e y| ≤
          ∫ y in -Real.pi..Real.pi, |H y * e y| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ = ∫ y in -Real.pi..Real.pi, H y * |e y| := by
        apply intervalIntegral.integral_congr
        intro y _
        change |H y * e y| = H y * |e y|
        rw [abs_mul, abs_of_nonneg (hHnonneg y)]
  have hHE :
      (∫ y in -Real.pi..Real.pi, H y * |e y|) ≤
        ∫ y in -Real.pi..Real.pi, H y * E := by
    apply intervalIntegral.integral_mono_on hab
    · exact (hHcont.mul he.abs).intervalIntegrable _ _
    · exact (hHcont.mul continuous_const).intervalIntegrable _ _
    · intro y hy
      exact mul_le_mul_of_nonneg_left (hbound y hy) (hHnonneg y)
  have hHint :
      (∫ y in -Real.pi..Real.pi, H y) ≤
        2 * Real.pi * rate := by
    have hsplit :
        (∫ y in -Real.pi..Real.pi, H y) =
          2 * Real.pi - floor *
            (∫ y in -Real.pi..Real.pi,
              1 / sixVertexRootDensityWeight c y) := by
      rw [show H = fun y =>
          sixVertexRootDensityKernel c x y /
              sixVertexRootDensityWeight c y -
            floor * (1 / sixVertexRootDensityWeight c y) by
        funext y
        dsimp [H]
        ring]
      have hsubint := intervalIntegral.integral_sub (μ := MeasureTheory.volume)
          (hkernelQuotCont.intervalIntegrable (-Real.pi) Real.pi)
          (hfloorInvCont.intervalIntegrable (-Real.pi) Real.pi)
      change (∫ y in -Real.pi..Real.pi,
          sixVertexRootDensityKernel c x y /
              sixVertexRootDensityWeight c y -
            floor * (1 / sixVertexRootDensityWeight c y)) =
        (∫ y in -Real.pi..Real.pi,
          sixVertexRootDensityKernel c x y /
            sixVertexRootDensityWeight c y) -
          ∫ y in -Real.pi..Real.pi,
            floor * (1 / sixVertexRootDensityWeight c y) at hsubint
      rw [hsubint, intervalIntegral.integral_const_mul,
        intervalIntegral_sixVertexRootDensityKernel_div_weight hc]
    have hvol := intervalIntegral_one_div_sixVertexRootDensityWeight_lower hc
    have hmul := mul_le_mul_of_nonneg_left hvol hfloor.le
    calc
      (∫ y in -Real.pi..Real.pi, H y) =
          2 * Real.pi - floor *
            (∫ y in -Real.pi..Real.pi,
              1 / sixVertexRootDensityWeight c y) := hsplit
      _ ≤ 2 * Real.pi - floor *
          (2 * Real.pi * (sixVertexRootDensityScale c /
            (sixVertexAnisotropyMagnitude c + 1))) :=
        sub_le_sub_left hmul _
      _ = 2 * Real.pi * rate := by
        dsimp [rate, sixVertexRootDensityContractionRate]
        ring
  rw [hHeq]
  have htotal :
      |∫ y in -Real.pi..Real.pi, H y * e y| ≤
        2 * Real.pi * rate * E := by
    calc
      _ ≤ ∫ y in -Real.pi..Real.pi, H y * |e y| := habsolute
      _ ≤ ∫ y in -Real.pi..Real.pi, H y * E := hHE
      _ = (∫ y in -Real.pi..Real.pi, H y) * E := by
        rw [intervalIntegral.integral_mul_const]
      _ ≤ (2 * Real.pi * rate) * E :=
        mul_le_mul_of_nonneg_right hHint hE
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hpi)]
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hpi]
  calc
    |∫ y in -Real.pi..Real.pi, H y * e y| ≤
        2 * Real.pi * rate * E := htotal
    _ = sixVertexRootDensityContractionRate c * E * (2 * Real.pi) := by
      dsimp [rate]
      ring

end
end StatMech.FrontierD
