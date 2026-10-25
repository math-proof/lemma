/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricJacobian.Part3
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootDensityKernel
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexRootDensityScale_pos
    {c : Real} (hc : 2 < c) : 0 < sixVertexRootDensityScale c := by
  have hd := one_lt_sixVertexAnisotropyMagnitude hc
  unfold sixVertexRootDensityScale
  exact Real.sqrt_pos.2 (by nlinarith)

theorem sixVertexRootDensityWeight_pos
    {c : Real} (hc : 2 < c) (x : Real) :
    0 < sixVertexRootDensityWeight c x := by
  exact div_pos (sixVertexBetheIntegratingFactor_pos hc x)
    (sixVertexRootDensityScale_pos hc)

theorem sixVertexRootDensityKernel_pos
    {c : Real} (hc : 2 < c) (x y : Real) :
    0 < sixVertexRootDensityKernel c x y := by
  have hd : 0 < sixVertexAnisotropyMagnitude c :=
    (one_lt_sixVertexAnisotropyMagnitude hc).trans' zero_lt_one
  unfold sixVertexRootDensityKernel
  apply div_pos
  · exact mul_pos
      (mul_pos (mul_pos (by positivity) hd)
        (sixVertexBetheIntegratingFactor_pos hc x))
      (sixVertexBetheIntegratingFactor_pos hc y)
  · exact mul_pos (sixVertexRootDensityScale_pos hc)
      (sixVertexThetaDerivativeDenominator_pos hc x y)

theorem sixVertexRootDensityKernelFloor_pos
    {c : Real} (hc : 2 < c) :
    0 < sixVertexRootDensityKernelFloor c := by
  let d := sixVertexAnisotropyMagnitude c
  let s := sixVertexRootDensityScale c
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hs : 0 < s := sixVertexRootDensityScale_pos hc
  dsimp [sixVertexRootDensityKernelFloor]
  positivity

theorem sixVertexBetheIntegratingFactor_bounds
    {c : Real} (hc : 2 < c) (x : Real) :
    sixVertexAnisotropyMagnitude c - 1 ≤
        sixVertexBetheIntegratingFactor c x ∧
      sixVertexBetheIntegratingFactor c x ≤
        sixVertexAnisotropyMagnitude c + 1 := by
  have hlo := Real.neg_one_le_cos x
  have hhi := Real.cos_le_one x
  simp only [sixVertexAnisotropyMagnitude, sixVertexBetheIntegratingFactor]
  constructor <;> linarith

theorem sixVertexThetaDerivativeDenominator_uniform_upper
    {c : Real} (hc : 2 < c) (x y : Real) :
    sixVertexThetaDerivativeDenominator c x y ≤
      4 * (sixVertexAnisotropyMagnitude c + 1) ^ 2 + 4 := by
  rw [sixVertexThetaDerivativeDenominator_eq]
  have hx := sixVertexBetheIntegratingFactor_bounds hc x
  have hy := sixVertexBetheIntegratingFactor_bounds hc y
  have hfx : 0 ≤ sixVertexBetheIntegratingFactor c x :=
    (sixVertexBetheIntegratingFactor_pos hc x).le
  have hfy : 0 ≤ sixVertexBetheIntegratingFactor c y :=
    (sixVertexBetheIntegratingFactor_pos hc y).le
  have hd1 : 0 ≤ sixVertexAnisotropyMagnitude c + 1 := by
    linarith [one_lt_sixVertexAnisotropyMagnitude hc]
  have hprod : sixVertexBetheIntegratingFactor c x *
      sixVertexBetheIntegratingFactor c y ≤
        (sixVertexAnisotropyMagnitude c + 1) ^ 2 := by
    nlinarith [mul_le_mul hx.2 hy.2 hfy hd1]
  have hcos := Real.neg_one_le_cos (x - y)
  nlinarith

theorem sixVertexRootDensityKernelFloor_le
    {c : Real} (hc : 2 < c) (x y : Real) :
    sixVertexRootDensityKernelFloor c ≤
      sixVertexRootDensityKernel c x y := by
  let d := sixVertexAnisotropyMagnitude c
  let s := sixVertexRootDensityScale c
  let Fx := sixVertexBetheIntegratingFactor c x
  let Fy := sixVertexBetheIntegratingFactor c y
  let D := sixVertexThetaDerivativeDenominator c x y
  let U := 4 * (d + 1) ^ 2 + 4
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hs : 0 < s := sixVertexRootDensityScale_pos hc
  have hFx : 0 < Fx := sixVertexBetheIntegratingFactor_pos hc x
  have hFy : 0 < Fy := sixVertexBetheIntegratingFactor_pos hc y
  have hD : 0 < D := sixVertexThetaDerivativeDenominator_pos hc x y
  have hU : 0 < U := by dsimp [U]; positivity
  have hFxlo : d - 1 ≤ Fx := (sixVertexBetheIntegratingFactor_bounds hc x).1
  have hFylo : d - 1 ≤ Fy := (sixVertexBetheIntegratingFactor_bounds hc y).1
  have hDle : D ≤ U := sixVertexThetaDerivativeDenominator_uniform_upper hc x y
  have hprod : (d - 1) ^ 2 ≤ Fx * Fy := by
    nlinarith [mul_le_mul hFxlo hFylo (sub_nonneg.mpr hd.le) hFx.le]
  change 4 * d * (d - 1) ^ 2 / (s * U) ≤
    4 * d * Fx * Fy / (s * D)
  rw [div_le_div_iff₀ (mul_pos hs hU) (mul_pos hs hD)]
  have hd0 : 0 ≤ 4 * d * s := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hprod hd0,
    mul_le_mul_of_nonneg_left hDle (by positivity : 0 ≤ 4 * d * Fx * Fy * s)]


theorem sixVertexRootDensityKernel_div_weight
    {c : Real} (hc : 2 < c) (x y : Real) :
    sixVertexRootDensityKernel c x y /
        sixVertexRootDensityWeight c y =
      -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
        sixVertexThetaDerivativeDenominator c x y := by
  have hs := (sixVertexRootDensityScale_pos hc).ne'
  have hFy := (sixVertexBetheIntegratingFactor_pos hc y).ne'
  unfold sixVertexRootDensityKernel sixVertexRootDensityWeight
    sixVertexAnisotropyMagnitude
  field_simp


theorem sixVertexRootDensityKernel_eq_neg_weight_mul_leftDerivative
    {c : Real} (hc : 2 < c) (x y : Real) :
    sixVertexRootDensityKernel c x y =
      -sixVertexRootDensityWeight c x *
        (4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
          sixVertexThetaDerivativeDenominator c x y) := by
  have hs := (sixVertexRootDensityScale_pos hc).ne'
  unfold sixVertexRootDensityKernel sixVertexRootDensityWeight
    sixVertexAnisotropyMagnitude
  field_simp


theorem intervalIntegral_sixVertexRootDensityKernel_div_weight
    {c : Real} (hc : 2 < c) (x : Real) :
    ∫ y in -Real.pi..Real.pi,
        sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y = 2 * Real.pi := by
  let f : Real → Real := fun y => sixVertexTheta c x y
  let f' : Real → Real := fun y =>
    -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
      sixVertexThetaDerivativeDenominator c x y
  have hfderiv : deriv f = f' := by
    funext y
    exact (hasDerivAt_sixVertexTheta_right hc x y).deriv
  have hfdiff : ∀ y ∈ Set.uIcc (-Real.pi) Real.pi,
      DifferentiableAt Real f y := by
    intro y _
    exact (hasDerivAt_sixVertexTheta_right hc x y).differentiableAt
  have hfcont : ContinuousOn f' (Set.uIcc (-Real.pi) Real.pi) := by
    apply Continuous.continuousOn
    dsimp [f']
    apply Continuous.div
    · fun_prop
    · unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
      fun_prop
    · intro y
      exact (sixVertexThetaDerivativeDenominator_pos hc x y).ne'
  have hFTC := intervalIntegral.integral_deriv_eq_sub'
    (a := -Real.pi) (b := Real.pi) f hfderiv hfdiff hfcont
  have hend : f Real.pi - f (-Real.pi) = 2 * Real.pi := by
    have hperiod := sixVertexTheta_add_two_pi_right c x (-Real.pi)
    have harg : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [harg] at hperiod
    dsimp [f]
    linarith
  rw [hend] at hFTC
  calc
    (∫ y in -Real.pi..Real.pi,
        sixVertexRootDensityKernel c x y /
          sixVertexRootDensityWeight c y) =
        ∫ y in -Real.pi..Real.pi, f' y := by
          apply intervalIntegral.integral_congr
          intro y _
          exact sixVertexRootDensityKernel_div_weight hc x y
    _ = 2 * Real.pi := hFTC


end
end StatMech.FrontierD
