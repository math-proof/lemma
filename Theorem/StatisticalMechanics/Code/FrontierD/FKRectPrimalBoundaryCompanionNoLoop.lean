/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryCompanionNoLoop.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryCompanionUnique
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveMixedNoLoopHeight
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryCompanionNoLoop


namespace StatMech.FrontierD

noncomputable section

theorem zeroTurnCost_div_two_q_le_allSectorNormalization_of_companionUnique_height
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (hunique : forall omega : R.Configuration,
      ¬ FKRectHasNet R omega ->
        FKRectPrimalBoundaryCompanionUnique R omega)
    (hextreme : forall omega : R.Configuration,
      FKRectPrimalDevelopedExtremeSameSign R omega)
    (hdual : forall omega : R.Configuration,
      FKRectZeroTurnOriginalDualSameSideUnique R omega) :
    (2 / Real.sqrt q) ^ (2 * R.width + 2 * R.height + 2) / (2 * q) <=
      fkRectAllSectorNormalization R q := by
  apply zeroTurnCost_div_two_q_le_allSectorNormalization_of_regularNeighborhood_height
    R hq
  · intro omega
    exact FKRectPrimalRankOneRegularNeighborhood.ofCompanionUnique
      R omega (hunique omega) (hextreme omega)
  · exact hdual

end
end StatMech.FrontierD
