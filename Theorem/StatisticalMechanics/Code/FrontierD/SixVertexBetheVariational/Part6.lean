/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part7
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part6
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem hasFDerivAt_sixVertexNormalizedTheta {c : ℝ} (hc : 2 < c)
    (x y : ℝ) :
    HasFDerivAt (fun xy : ℝ × ℝ =>
      sixVertexNormalizedTheta c xy.1 xy.2)
      (fderiv ℝ (fun xy : ℝ × ℝ =>
        sixVertexNormalizedTheta c xy.1 xy.2) (x, y)) (x, y) := by
  apply DifferentiableAt.hasFDerivAt
  unfold sixVertexNormalizedTheta
  have hx : DifferentiableAt ℝ (fun xy : ℝ × ℝ => xy.1) (x, y) := by fun_prop
  have hden : DifferentiableAt ℝ
      (fun xy : ℝ × ℝ => sixVertexBetheIntegratingFactor c xy.1) (x, y) := by
    unfold sixVertexBetheIntegratingFactor
    exact ((Real.hasDerivAt_cos x).comp_hasFDerivAt (x, y)
      hx.hasFDerivAt).differentiableAt.sub_const _
  have hinv := (hasFDerivAt_inv
    (sixVertexBetheIntegratingFactor_pos hc x).ne').comp
      (x, y) hden.hasFDerivAt
  simpa only [div_eq_mul_inv] using
    (hasFDerivAt_sixVertexTheta hc x y).differentiableAt.mul
      hinv.differentiableAt

@[fun_prop] theorem differentiable_sixVertexNormalizedTheta
    {c : ℝ} (hc : 2 < c) :
    Differentiable ℝ (fun xy : ℝ × ℝ =>
      sixVertexNormalizedTheta c xy.1 xy.2) := by
  intro xy
  exact (hasFDerivAt_sixVertexNormalizedTheta hc xy.1 xy.2).differentiableAt

theorem hasDerivAt_sixVertexNormalizedTheta_right
    {c : ℝ} (hc : 2 < c) (x y : ℝ) :
    HasDerivAt (fun t => sixVertexNormalizedTheta c x t)
      ((-4 * sixVertexDelta c) /
        sixVertexThetaDerivativeDenominator c x y) y := by
  unfold sixVertexNormalizedTheta
  have h := (hasDerivAt_sixVertexTheta_right hc x y).div_const
    (sixVertexBetheIntegratingFactor c x)
  convert h using 1
  exact (sixVertexTheta_mixed_integratingFactor hc x y).symm


end
end StatMech.FrontierD
