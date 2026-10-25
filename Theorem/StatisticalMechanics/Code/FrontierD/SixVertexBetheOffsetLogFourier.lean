/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronFourierLimit
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetLogSingularity.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetProfileRegularity.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetLogFourier


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

theorem hasDerivAt_sixVertexRegularizedBetheLogKernel
    {c epsilon x : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    HasDerivAt (sixVertexRegularizedBetheLogKernel c epsilon)
      (sixVertexRegularizedBetheLogNormDerivative c epsilon x) x := by
  let a := c ^ 2 - 1
  let A : Real -> Real := fun y => a ^ 2 + 1 + 2 * a * Real.cos y
  let B : Real -> Real := fun y => 2 - 2 * Real.cos y + epsilon
  have ha : 1 < a := by dsimp [a]; nlinarith
  have hA : 0 < A x := by
    dsimp [A]
    nlinarith [Real.neg_one_le_cos x, sq_nonneg (a - 1)]
  have hB : 0 < B x := by
    dsimp [B]
    nlinarith [Real.cos_le_one x]
  have hAderiv : HasDerivAt A (-2 * a * Real.sin x) x := by
    dsimp [A]
    convert (Real.hasDerivAt_cos x).const_mul (2 * a) |>.const_add (a ^ 2 + 1)
      using 1 <;> ring
  have hBderiv : HasDerivAt B (2 * Real.sin x) x := by
    convert (Real.hasDerivAt_cos x).const_mul (-2) |>.const_add (2 + epsilon)
      using 1
    · funext y
      dsimp [B]
      ring
    · ring
  have h := ((hAderiv.log hA.ne').sub (hBderiv.log hB.ne')).const_mul
    (1 / 2 : Real)
  unfold sixVertexRegularizedBetheLogKernel
    sixVertexBetheLogNumerator sixVertexBetheLogDenominator
    sixVertexRegularizedBetheLogNormDerivative
  dsimp [a, A, B] at h ⊢
  convert h using 1 <;> field_simp [hA.ne', hB.ne'] <;> ring

end
end StatMech.FrontierD
