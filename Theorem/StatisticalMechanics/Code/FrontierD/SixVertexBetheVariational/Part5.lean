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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part5
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexNormalizedBetheResidual_eq_zero_iff
    {c : ℝ} (hc : 2 < c) (N n : ℕ) (p : Fin n → ℝ) :
    (∀ j, sixVertexNormalizedBetheResidual c N n p j = 0) ↔
      SixVertexSatisfiesBetheEquations c N n p := by
  rw [← sixVertexBetheResidual_eq_zero_iff]
  apply forall_congr'
  intro j
  unfold sixVertexNormalizedBetheResidual
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact False.elim ((sixVertexBetheIntegratingFactor_pos hc (p j)).ne' h)
  · intro h
    simp [h]


theorem sixVertexTheta_mixed_integratingFactor {c : ℝ} (hc : 2 < c)
    (x y : ℝ) :
    (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
          sixVertexThetaDerivativeDenominator c x y) /
        sixVertexBetheIntegratingFactor c x =
      (-4 * sixVertexDelta c) /
        sixVertexThetaDerivativeDenominator c x y := by
  field_simp [(sixVertexBetheIntegratingFactor_pos hc x).ne']

theorem sixVertexTheta_mixed_integratingFactor_symm
    {c : ℝ} (hc : 2 < c) (x y : ℝ) :
    (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
          sixVertexThetaDerivativeDenominator c x y) /
        sixVertexBetheIntegratingFactor c x =
      (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
          sixVertexThetaDerivativeDenominator c y x) /
        sixVertexBetheIntegratingFactor c y := by
  rw [sixVertexTheta_mixed_integratingFactor hc,
    sixVertexTheta_mixed_integratingFactor hc,
    sixVertexThetaDerivativeDenominator_swap]


end
end StatMech.FrontierD
