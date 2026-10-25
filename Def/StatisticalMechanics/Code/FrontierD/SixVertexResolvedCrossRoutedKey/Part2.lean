/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedCrossRoutedKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedCrossRoutedKey


namespace StatMech.FrontierD

noncomputable section

noncomputable def FKColoredResolvedUnitCross.toFineTwoCycleRoutedKey
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (cross : FKColoredResolvedUnitCross source) :
    FKColoredFineTwoCycleUnitTransferRoutedKey source := by
  let splice := FKColoredStrandSplice.ofIndexedOccurrences source
    (fun layer => (source layer).pairing)
    (Fintype.card (FKColoredVertexCrossOccurrence cross.mask))
    (fkColoredVertexCrossOccurrenceKey cross.mask)
    (fkColoredVertexCrossOccurrenceKey_injective cross.mask)
    cross.boundaryIntertwining
  have htarget : splice.target = cross.target := cross.indexedSplice_target
  refine
    { targetPairing := fun layer => (source layer).pairing
      occurrenceCount := Fintype.card
        (FKColoredVertexCrossOccurrence cross.mask)
      key := fkColoredVertexCrossOccurrenceKey cross.mask
      key_injective := fkColoredVertexCrossOccurrenceKey_injective cross.mask
      boundaryIntertwining := cross.boundaryIntertwining
      preservesTotalC := ?_
      seamDelta_false := ?_
      seamDelta_true := ?_
      fine := ?_
      twoCycle := ?_ }
  · unfold FKColoredStrandSplice.PreservesTotalC
    rw [← fkColoredLoopPairingPairTotalC_eq_slotPairEqualCount,
      ← splice.target_totalC_eq_slotPairEqualCount,
      htarget]
    exact fkColoredVertexCrossTarget_totalC source cross.mask
      cross.bondCoherent
  · unfold FKColoredStrandSplice.seamDelta
    rw [htarget]
    exact cross.seamDelta_false
  · unfold FKColoredStrandSplice.seamDelta
    rw [htarget]
    exact cross.seamDelta_true
  · change sixVertexHorizontalPairBoundedFineRowProfile
        ((splice.target false).arrows.horizontal,
          (splice.target true).arrows.horizontal) = _
    have hprofile := congrArg
      (fun target : FKColoredLoopPairingPair T =>
        sixVertexHorizontalPairBoundedFineRowProfile
          ((target false).arrows.horizontal,
            (target true).arrows.horizontal)) htarget
    exact hprofile.trans cross.target_fine
  · change sixVertexPairAtMostTwoCycleRelated
        ((source false).arrows, (source true).arrows)
        ((splice.target false).arrows, (splice.target true).arrows)
    rw [congrFun htarget false, congrFun htarget true]
    exact cross.twoCycle

end
end StatMech.FrontierD
