/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBetheOne.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhase.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem hasDerivAt_sixVertexTheta_zero_left
    {c : Real} (hc : 2 < c) (y : Real) :
    HasDerivAt (fun x => sixVertexTheta c x y)
      (sixVertexThetaLeftDerivAtZero c y) 0 := by
  simpa [sixVertexThetaLeftDerivAtZero,
    sixVertexBetheIntegratingFactor,
    sixVertexThetaDerivativeDenominator] using
      hasDerivAt_sixVertexTheta_left hc 0 y

theorem sixVertexThetaLeftDerivAtZero_self
    {c : Real} (hc : 2 < c) :
    sixVertexThetaLeftDerivAtZero c 0 = 2 / c ^ 2 - 1 := by
  have hc0 : c ≠ 0 := by linarith
  have hint : sixVertexBetheIntegratingFactor c 0 = c ^ 2 / 2 := by
    unfold sixVertexBetheIntegratingFactor sixVertexDelta
    rw [Real.cos_zero]
    ring
  have hden : sixVertexThetaDerivativeDenominator c 0 0 = c ^ 4 := by
    unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
      sixVertexDelta
    rw [Real.cos_zero, Real.sin_zero]
    ring
  rw [sixVertexThetaLeftDerivAtZero, hint, hden]
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0
  field_simp [hc2]
  unfold sixVertexDelta
  ring


theorem neg_two_lt_sixVertexThetaLeftDerivAtZero
    {c : Real} (hc : 2 < c) (y : Real) :
    -2 < sixVertexThetaLeftDerivAtZero c y := by
  let a : Real := -sixVertexDelta c
  let t : Real := Real.cos y
  have ha : 1 < a := by
    dsimp [a]
    nlinarith [sixVertexDelta_lt_neg_one hc]
  have htLower : -1 <= t := Real.neg_one_le_cos y
  have htUpper : t <= 1 := Real.cos_le_one y
  have hsin := Real.sin_sq_add_cos_sq y
  have hden : 0 < sixVertexThetaDerivativeDenominator c 0 y :=
    sixVertexThetaDerivativeDenominator_pos hc 0 y
  have hgap :
      2 * a * (t + a) < sixVertexThetaDerivativeDenominator c 0 y := by
    dsimp [a, t, sixVertexThetaDerivativeDenominator,
      sixVertexThetaDenominator]
    simp only [Real.cos_zero, Real.sin_zero, zero_sub]
    nlinarith [mul_pos (by linarith : 0 < a + 1)
      (by linarith : 0 < a + 1 + Real.cos y)]
  unfold sixVertexThetaLeftDerivAtZero sixVertexBetheIntegratingFactor
  rw [lt_div_iff₀ hden]
  dsimp [a, t] at hgap
  nlinarith


end
end StatMech.FrontierD
