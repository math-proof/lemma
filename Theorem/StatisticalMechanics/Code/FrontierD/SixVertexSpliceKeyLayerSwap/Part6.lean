/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part6


namespace StatMech.FrontierD

noncomputable section

namespace FKColoredFineTwoCycleUnitTransferSpliceKey

@[simp] theorem swap_target
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source)
    (hsource : SourceSeamDifferenceTwo source) :
    (key.swap hsource).splice.target =
      fkColoredLoopPairingPairSwapLayers key.splice.target :=
  key.swapSplice_target


end FKColoredFineTwoCycleUnitTransferSpliceKey
end
end StatMech.FrontierD
