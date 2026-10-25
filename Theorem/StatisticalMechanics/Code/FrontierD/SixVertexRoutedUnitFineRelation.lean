/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedUnitFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedUnitCrossFineRelation.Part6
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexResolvedRoutedKey
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation


namespace StatMech.FrontierD

noncomputable section

namespace FKColoredFineTwoCycleUnitTransferRoutedKey

theorem target_bigrade
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey source) :
    (fkColoredLoopPairingPairTotalC key.splice.target,
        fkColoredTrueStrandSlotCount key.splice.target) =
      (fkColoredLoopPairingPairTotalC source,
        fkColoredTrueStrandSlotCount source) :=
  key.toFKColoredUnitTransferRoutedKey.target_bigrade

theorem target_fine
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey source) :
    sixVertexHorizontalPairBoundedFineRowProfile
        ((key.splice.target false).arrows.horizontal,
          (key.splice.target true).arrows.horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        ((source false).arrows.horizontal,
          (source true).arrows.horizontal) :=
  key.fine

theorem target_twoCycleFine
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey source) :
    sixVertexPairAtMostTwoCycleFineRelated
      ((source false).arrows, (source true).arrows)
      ((key.splice.target false).arrows,
        (key.splice.target true).arrows) :=
  ⟨key.twoCycle, key.fine.symm⟩

end FKColoredFineTwoCycleUnitTransferRoutedKey
end
end StatMech.FrontierD
