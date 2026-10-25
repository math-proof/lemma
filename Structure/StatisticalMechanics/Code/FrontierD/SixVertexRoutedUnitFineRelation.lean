/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedUnitFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedUnitCrossFineRelation.Part6
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexResolvedRoutedKey
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation


namespace StatMech.FrontierD

noncomputable section

structure FKColoredFineTwoCycleUnitTransferRoutedKey
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    extends FKColoredUnitTransferRoutedKey source where
  fine : sixVertexHorizontalPairBoundedFineRowProfile
      (((toFKColoredUnitTransferRoutedKey.splice.target false).arrows.horizontal),
        ((toFKColoredUnitTransferRoutedKey.splice.target true).arrows.horizontal)) =
    sixVertexHorizontalPairBoundedFineRowProfile
      ((source false).arrows.horizontal, (source true).arrows.horizontal)
  twoCycle : sixVertexPairAtMostTwoCycleRelated
    ((source false).arrows, (source true).arrows)
    ((toFKColoredUnitTransferRoutedKey.splice.target false).arrows,
      (toFKColoredUnitTransferRoutedKey.splice.target true).arrows)

end
end StatMech.FrontierD
