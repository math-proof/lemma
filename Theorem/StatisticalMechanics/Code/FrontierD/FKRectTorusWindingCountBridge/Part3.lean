/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusAllChargeReduction
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnClassification.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerDefectClassification
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge.Part3


namespace StatMech.FrontierD

noncomputable section

theorem fkRectZeroTurnEulerResidual_nonneg
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (omega : R.Configuration) :
    0 ≤ fkRectZeroTurnEulerResidual R q omega := by
  unfold fkRectZeroTurnEulerResidual
  positivity

theorem fkRectZeroTurnEulerResidual_le_one
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (omega : R.Configuration) :
    fkRectZeroTurnEulerResidual R q omega ≤ 1 := by
  have hq0 : 0 ≤ q := by linarith
  have hspos : 0 < Real.sqrt q := Real.sqrt_pos.2 (by linarith)
  have hs2 : 2 ≤ Real.sqrt q := by
    nlinarith [Real.sq_sqrt hq0, Real.sqrt_nonneg q]
  have hb0 : 0 ≤ 2 / Real.sqrt q := by positivity
  have hb1 : 2 / Real.sqrt q ≤ 1 :=
    (div_le_one hspos).2 hs2
  have hpow : (2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega ≤ 1 :=
    pow_le_one₀ hb0 hb1
  have hdef := fkRectEulerHomologyDefect_classified R
    (fkRectOpenEdges R omega)
  rw [fkRectConfigurationOfEdges_openEdges] at hdef
  rcases hdef with hzero | htwo
  · simpa [fkRectZeroTurnEulerResidual, hzero] using hpow
  · unfold fkRectZeroTurnEulerResidual
    rw [htwo]
    have hden : Real.sqrt q ^ (2 : Int) = q := by
      simpa only [zpow_ofNat] using Real.sq_sqrt hq0
    rw [hden]
    exact (div_le_one (by linarith)).2 (hpow.trans (by linarith))


end
end StatMech.FrontierD
