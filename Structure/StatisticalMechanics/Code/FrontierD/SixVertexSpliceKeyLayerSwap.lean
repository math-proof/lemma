/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part2


namespace StatMech.FrontierD

noncomputable section

structure FKColoredFineTwoCycleUnitTransferSpliceKey
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) where
  splice : FKColoredStrandSplice source
  preservesTotalC : splice.PreservesTotalC
  seamDelta_false : splice.seamDelta false = 1
  seamDelta_true : splice.seamDelta true = -1
  fine :
    sixVertexHorizontalPairBoundedFineRowProfile
        ((splice.target false).arrows.horizontal,
          (splice.target true).arrows.horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        ((source false).arrows.horizontal,
          (source true).arrows.horizontal)
  twoCycle :
    sixVertexPairAtMostTwoCycleRelated
      ((source false).arrows, (source true).arrows)
      ((splice.target false).arrows, (splice.target true).arrows)

end
end StatMech.FrontierD
