/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullMaskSpliceKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part7


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexFullUnitMaskSplice
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask) :
    FKColoredStrandSplice source := by
  let target := sixVertexFullDisagreementColoredTarget source mask hmask
  have hcount : fkColoredTrueStrandSlotCount source =
      fkColoredTrueStrandSlotCount target := by
    exact (congrArg Prod.snd
      (sixVertexFullDisagreementColoredTarget_bigrade
        source mask hmask)).symm
  exact FKColoredStrandSplice.ofColorEquiv source target
    (fkColoredStrandSlotEquivOfTrueCount source target hcount)
    (fkColoredStrandSlotEquivOfTrueCount_color source target hcount)

end
end StatMech.FrontierD
