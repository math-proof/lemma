/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullMaskSpliceKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFullMaskSpliceKey.Part2


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexFullUnitMaskSpliceKey_target
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (source false).arrows (source true).arrows = 1) :
    (sixVertexFullUnitMaskSpliceKey source mask hmask htransfer).splice.target =
      sixVertexFullDisagreementColoredTarget source mask hmask :=
  sixVertexFullUnitMaskSplice_target source mask hmask

end
end StatMech.FrontierD
