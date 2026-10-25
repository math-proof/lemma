/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedKeySlotColorInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySlotColorInvariant


namespace StatMech.FrontierD

noncomputable section

def FKColoredFineTwoCycleUnitTransferRoutedKey.ofSlotColorInvariant
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hinvariant : FKColoredIndexedOccurrenceSlotColorInvariant
      source targetPairing n key hinjective)
    (hTotalC : (fkColoredSlotColorInvariantSplice source targetPairing n
      key hinjective hinvariant).PreservesTotalC)
    (hfalse : (fkColoredSlotColorInvariantSplice source targetPairing n
      key hinjective hinvariant).seamDelta false = 1)
    (htrue : (fkColoredSlotColorInvariantSplice source targetPairing n
      key hinjective hinvariant).seamDelta true = -1)
    (hfine : sixVertexHorizontalPairBoundedFineRowProfile
        (((fkColoredSlotColorInvariantSplice source targetPairing n key
          hinjective hinvariant).target false).arrows.horizontal,
        ((fkColoredSlotColorInvariantSplice source targetPairing n key
          hinjective hinvariant).target true).arrows.horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        ((source false).arrows.horizontal, (source true).arrows.horizontal))
    (htwoCycle : sixVertexPairAtMostTwoCycleRelated
      ((source false).arrows, (source true).arrows)
      (((fkColoredSlotColorInvariantSplice source targetPairing n key
          hinjective hinvariant).target false).arrows,
        ((fkColoredSlotColorInvariantSplice source targetPairing n key
          hinjective hinvariant).target true).arrows)) :
    FKColoredFineTwoCycleUnitTransferRoutedKey source :=
  { toFKColoredUnitTransferRoutedKey :=
      FKColoredUnitTransferRoutedKey.ofSlotColorInvariant source
        targetPairing n key hinjective hinvariant hTotalC hfalse htrue
    fine := hfine
    twoCycle := htwoCycle }

end
end StatMech.FrontierD
