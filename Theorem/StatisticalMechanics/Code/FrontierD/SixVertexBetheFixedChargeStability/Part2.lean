/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheInfiniteAnisotropyGauge
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeStability


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexRootDensityKernelUniformBound_nonneg
    {c : Real} (hc : 2 < c) :
    0 ≤ sixVertexRootDensityKernelUniformBound c := by
  unfold sixVertexRootDensityKernelUniformBound
  have hd := one_lt_sixVertexAnisotropyMagnitude hc
  have hs := sixVertexRootDensityScale_pos hc
  positivity

theorem abs_sixVertexRootDensityKernel_le_uniformBound
    {c : Real} (hc : 2 < c) (x y : Real) :
    |sixVertexRootDensityKernel c x y| ≤
      sixVertexRootDensityKernelUniformBound c := by
  have hwpos := sixVertexRootDensityWeight_pos hc y
  have hwle := sixVertexRootDensityWeight_le hc y
  have hk := abs_sixVertexRootDensityKernel_div_weight_le hc x y
  have hratio : 0 ≤ sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1) := by
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  calc
    |sixVertexRootDensityKernel c x y| =
        |(sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y) *
            sixVertexRootDensityWeight c y| := by
      rw [div_mul_cancel₀ _ hwpos.ne']
    _ = |sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y| *
            sixVertexRootDensityWeight c y := by
      rw [abs_mul, abs_of_pos hwpos]
    _ ≤ (sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1)) *
        ((sixVertexAnisotropyMagnitude c + 1) /
          sixVertexRootDensityScale c) :=
      mul_le_mul hk hwle hwpos.le hratio
    _ = sixVertexRootDensityKernelUniformBound c := rfl

theorem sixVertexRootDensityKernel_contraction_of_fixedMass
    {c : Real} (hc : 2 < c) {e : Real → Real} {E m : Real}
    (he : Continuous e) (hE : 0 ≤ E) (hm : 0 ≤ m)
    (hmass : (∫ y in -Real.pi..Real.pi,
      e y / sixVertexRootDensityWeight c y) = m)
    (hbound : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |e y| ≤ E)
    (x : Real) :
    |(1 / (2 * Real.pi)) *
        ∫ y in -Real.pi..Real.pi,
          (sixVertexRootDensityKernel c x y /
            sixVertexRootDensityWeight c y) * e y| ≤
      sixVertexRootDensityContractionRate c *
          (E + (m / (2 * Real.pi)) *
            ((sixVertexAnisotropyMagnitude c + 1) /
              sixVertexRootDensityScale c)) +
        (m / (2 * Real.pi)) * sixVertexRootDensityKernelUniformBound c := by
  let alpha := m / (2 * Real.pi)
  let weightUpper := (sixVertexAnisotropyMagnitude c + 1) /
    sixVertexRootDensityScale c
  let M := alpha * weightUpper
  let e0 : Real → Real := fun y =>
    e y - alpha * sixVertexRootDensityWeight c y
  have hpi : 0 < 2 * Real.pi := by positivity
  have halpha : 0 ≤ alpha := div_nonneg hm hpi.le
  have hweightUpper : 0 ≤ weightUpper := by
    dsimp [weightUpper]
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    have hs := sixVertexRootDensityScale_pos hc
    positivity
  have hM : 0 ≤ M := mul_nonneg halpha hweightUpper
  have hweightCont : Continuous (sixVertexRootDensityWeight c) := by
    unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
      sixVertexRootDensityScale
    fun_prop
  have he0 : Continuous e0 :=
    he.sub (continuous_const.mul hweightCont)
  have he0Mass : ∫ y in -Real.pi..Real.pi,
      e0 y / sixVertexRootDensityWeight c y = 0 := by
    have heq : (fun y => e0 y / sixVertexRootDensityWeight c y) =
        fun y => e y / sixVertexRootDensityWeight c y - alpha := by
      funext y
      dsimp [e0]
      field_simp [(sixVertexRootDensityWeight_pos hc y).ne']
    have heQuot : Continuous (fun y =>
        e y / sixVertexRootDensityWeight c y) :=
      he.div hweightCont
        (fun y => (sixVertexRootDensityWeight_pos hc y).ne')
    rw [heq, intervalIntegral.integral_sub
      (heQuot.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), hmass]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    dsimp [alpha]
    field_simp [Real.pi_ne_zero]
    ring
  have he0Bound : ∀ y ∈ Set.Icc (-Real.pi) Real.pi,
      |e0 y| ≤ E + M := by
    intro y hy
    calc
      |e0 y| = |e y - alpha * sixVertexRootDensityWeight c y| := rfl
      _ ≤ |e y - 0| + |0 - alpha * sixVertexRootDensityWeight c y| :=
        abs_sub_le _ _ _
      _ = |e y| + |alpha * sixVertexRootDensityWeight c y| := by
        rw [sub_zero, zero_sub, abs_neg]
      _ ≤ E + M := by
        apply add_le_add (hbound y hy)
        rw [abs_mul, abs_of_nonneg halpha,
          abs_of_pos (sixVertexRootDensityWeight_pos hc y)]
        exact mul_le_mul_of_nonneg_left
          (sixVertexRootDensityWeight_le hc y) halpha
  have hcontract := sixVertexRootDensityKernel_contraction hc he0
    (add_nonneg hE hM) he0Mass he0Bound x
  have hkernelCont : Continuous (sixVertexRootDensityKernel c x) :=
    (lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous
  have he0QuotCont : Continuous (fun y =>
      (sixVertexRootDensityKernel c x y /
        sixVertexRootDensityWeight c y) * e0 y) := by
    apply Continuous.mul
    · exact hkernelCont.div hweightCont
        (fun y => (sixVertexRootDensityWeight_pos hc y).ne')
    · exact he0
  have hkernelIntegral :
      |∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c x y| ≤
        sixVertexRootDensityKernelUniformBound c * (2 * Real.pi) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -Real.pi) (b := Real.pi)
      (C := sixVertexRootDensityKernelUniformBound c)
      (f := sixVertexRootDensityKernel c x) (fun y _ => by
        simpa only [Real.norm_eq_abs] using
          abs_sixVertexRootDensityKernel_le_uniformBound hc x y)
    rw [Real.norm_eq_abs] at h
    convert h using 1
    rw [abs_of_pos]
    · ring
    · linarith [Real.pi_pos]
  have hrewrite :
      (∫ y in -Real.pi..Real.pi,
        (sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y) * e y) =
      (∫ y in -Real.pi..Real.pi,
        (sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y) * e0 y) +
        alpha * ∫ y in -Real.pi..Real.pi,
          sixVertexRootDensityKernel c x y := by
    calc
      (∫ y in -Real.pi..Real.pi,
        (sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y) * e y) =
          ∫ y in -Real.pi..Real.pi,
            (sixVertexRootDensityKernel c x y /
              sixVertexRootDensityWeight c y) * e0 y +
                alpha * sixVertexRootDensityKernel c x y := by
        apply intervalIntegral.integral_congr
        intro y _
        dsimp [e0]
        field_simp [(sixVertexRootDensityWeight_pos hc y).ne']
        ring
      _ = (∫ y in -Real.pi..Real.pi,
          (sixVertexRootDensityKernel c x y /
            sixVertexRootDensityWeight c y) * e0 y) +
          ∫ y in -Real.pi..Real.pi,
            alpha * sixVertexRootDensityKernel c x y := by
        exact intervalIntegral.integral_add
          (he0QuotCont.intervalIntegrable _ _)
          ((continuous_const.mul hkernelCont).intervalIntegrable _ _)
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  rw [hrewrite, mul_add]
  calc
    |(1 / (2 * Real.pi)) *
          (∫ y in -Real.pi..Real.pi,
            (sixVertexRootDensityKernel c x y /
              sixVertexRootDensityWeight c y) * e0 y) +
        (1 / (2 * Real.pi)) *
          (alpha * ∫ y in -Real.pi..Real.pi,
            sixVertexRootDensityKernel c x y)| ≤
        |(1 / (2 * Real.pi)) *
          (∫ y in -Real.pi..Real.pi,
            (sixVertexRootDensityKernel c x y /
              sixVertexRootDensityWeight c y) * e0 y)| +
        |(1 / (2 * Real.pi)) *
          (alpha * ∫ y in -Real.pi..Real.pi,
            sixVertexRootDensityKernel c x y)| := abs_add_le _ _
    _ ≤ sixVertexRootDensityContractionRate c * (E + M) +
        alpha * sixVertexRootDensityKernelUniformBound c := by
      apply add_le_add hcontract
      rw [abs_mul, abs_mul, abs_of_pos (one_div_pos.mpr hpi),
        abs_of_nonneg halpha]
      calc
        1 / (2 * Real.pi) *
            (alpha * |∫ y in -Real.pi..Real.pi,
              sixVertexRootDensityKernel c x y|) ≤
          1 / (2 * Real.pi) *
            (alpha * (sixVertexRootDensityKernelUniformBound c *
              (2 * Real.pi))) := by gcongr
        _ = alpha * sixVertexRootDensityKernelUniformBound c := by
          field_simp [Real.pi_ne_zero]
    _ = sixVertexRootDensityContractionRate c *
          (E + (m / (2 * Real.pi)) *
            ((sixVertexAnisotropyMagnitude c + 1) /
              sixVertexRootDensityScale c)) +
        (m / (2 * Real.pi)) *
          sixVertexRootDensityKernelUniformBound c := rfl

end
end StatMech.FrontierD
