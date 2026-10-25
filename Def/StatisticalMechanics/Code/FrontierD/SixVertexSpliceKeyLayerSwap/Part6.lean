/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part5


namespace StatMech.FrontierD

noncomputable section

namespace FKColoredFineTwoCycleUnitTransferSpliceKey

noncomputable def swap
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source)
    (hsource : SourceSeamDifferenceTwo source) :
    FKColoredFineTwoCycleUnitTransferSpliceKey source where
  splice := key.swapSplice
  preservesTotalC := key.swapSplice_preservesTotalC
  seamDelta_false := key.swapSplice_seamDelta_false hsource
  seamDelta_true := key.swapSplice_seamDelta_true hsource
  fine := by
    rw [key.swapSplice_target]
    exact (sixVertexSwapHorizontalLayers_boundedFineRowProfile
      ((key.splice.target false).arrows.horizontal,
        (key.splice.target true).arrows.horizontal)).trans key.fine
  twoCycle := by
    rw [key.swapSplice_target]
    exact sixVertexPairAtMostTwoCycleRelated_swap_target key.twoCycle

end FKColoredFineTwoCycleUnitTransferSpliceKey
end
end StatMech.FrontierD
