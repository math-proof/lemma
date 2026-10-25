/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopPairBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part11
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLoopPairBigrade.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLoopDecoratedPairBigrade_eq_configurationPair
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right) :
    sixVertexLoopDecoratedPairBigrade decorated =
      sixVertexConfigurationPairBigrade decorated.1 := by
  apply Prod.ext
  · rfl
  · exact sixVertexLoopDecoratedPairColored_trueSlotCount decorated

theorem sixVertexLoopDecoratedPairBigrade_eq_colored
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right) :
    sixVertexLoopDecoratedPairBigrade decorated =
      (fkColoredLoopPairingPairTotalC
          (sixVertexLoopDecoratedPairColored decorated),
        fkColoredTrueStrandSlotCount
          (sixVertexLoopDecoratedPairColored decorated)) := by
  unfold sixVertexLoopDecoratedPairBigrade
  rw [sixVertexLoopDecoratedPairColored_totalC]

end
end StatMech.FrontierD
