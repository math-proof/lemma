/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part3


namespace StatMech.FrontierD

noncomputable section

namespace FKColoredFineTwoCycleUnitTransferSpliceKey

noncomputable def swapSplice
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source) :
    FKColoredStrandSplice source := by
  let swapped := fkColoredLoopPairingPairSwapLayers key.splice.target
  have hcount : fkColoredTrueStrandSlotCount source =
      fkColoredTrueStrandSlotCount swapped := by
    exact (fkColoredLoopPairingPairSwapLayers_trueStrandSlotCount
      key.splice.target).trans key.splice.target_trueStrandSlotCount |>.symm
  exact FKColoredStrandSplice.ofColorEquiv source swapped
    (fkColoredStrandSlotEquivOfTrueCount source swapped hcount)
    (fkColoredStrandSlotEquivOfTrueCount_color source swapped hcount)

end FKColoredFineTwoCycleUnitTransferSpliceKey
end
end StatMech.FrontierD
