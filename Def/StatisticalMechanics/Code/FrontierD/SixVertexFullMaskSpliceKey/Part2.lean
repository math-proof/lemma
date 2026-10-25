/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullMaskSpliceKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullMaskSpliceKey


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexFullUnitMaskSpliceKey
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (source false).arrows (source true).arrows = 1) :
    FKColoredFineTwoCycleUnitTransferSpliceKey source where
  splice := sixVertexFullUnitMaskSplice source mask hmask
  preservesTotalC := sixVertexFullUnitMaskSplice_preservesTotalC
    source mask hmask
  seamDelta_false := sixVertexFullUnitMaskSplice_seamDelta_false
    source mask hmask htransfer
  seamDelta_true := sixVertexFullUnitMaskSplice_seamDelta_true
    source mask hmask htransfer
  fine := by
    rw [sixVertexFullUnitMaskSplice_target]
    exact sixVertexFullDisagreementColoredTarget_boundedFineRowProfile
      source mask hmask
  twoCycle := by
    rw [sixVertexFullUnitMaskSplice_target,
      sixVertexFullDisagreementColoredTarget_arrows,
      sixVertexFullDisagreementColoredTarget_arrows]
    exact hmask.pairAtMostTwoCycleFineRelated.1

end
end StatMech.FrontierD
