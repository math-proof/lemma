/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part4


namespace StatMech.FrontierD

noncomputable section

namespace FKColoredFineTwoCycleUnitTransferSpliceKey

@[simp] theorem swapSplice_target
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source) :
    key.swapSplice.target =
      fkColoredLoopPairingPairSwapLayers key.splice.target := by
  unfold swapSplice
  apply FKColoredStrandSplice.ofColorEquiv_target

theorem swapSplice_preservesTotalC
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source) :
    key.swapSplice.PreservesTotalC := by
  unfold FKColoredStrandSplice.PreservesTotalC
  rw [← key.swapSplice.target_totalC_eq_slotPairEqualCount,
    ← fkColoredLoopPairingPairTotalC_eq_slotPairEqualCount,
    key.swapSplice_target, fkColoredLoopPairingPairSwapLayers_totalC,
    key.splice.target_totalC key.preservesTotalC]


end FKColoredFineTwoCycleUnitTransferSpliceKey
end
end StatMech.FrontierD
