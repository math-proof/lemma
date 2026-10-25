/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedKeySourceRebase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySlotColorInvariant.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySourceRebase


namespace StatMech.FrontierD

noncomputable section

noncomputable def FKColoredFineTwoCycleUnitTransferRoutedKey.rebase
    {T : EvenTorus} {source rebased : FKColoredLoopPairingPair T}
    (certificate : FKColoredFineTwoCycleUnitTransferRoutedKey source)
    (hcolor : forall slot : FKLayeredStrandSlot T,
      fkColoredLayeredSlotColor rebased slot =
        fkColoredLayeredSlotColor source slot)
    (harrows : forall layer,
      (rebased layer).arrows = (source layer).arrows) :
    FKColoredFineTwoCycleUnitTransferRoutedKey rebased := by
  let routed := certificate.toFKColoredUnitTransferRoutedKey
  let hboundary := coloredIndexedOccurrenceBoundaryIntertwining_rebase
    source rebased routed.targetPairing routed.occurrenceCount routed.key
      routed.key_injective hcolor routed.boundaryIntertwining
  let rebasedSplice := FKColoredStrandSplice.ofIndexedOccurrences rebased
    routed.targetPairing routed.occurrenceCount routed.key
      routed.key_injective hboundary
  have htarget : rebasedSplice.target = routed.splice.target := by
    exact indexedOccurrenceSplice_target_rebase source rebased
      routed.targetPairing routed.occurrenceCount routed.key
      routed.key_injective hcolor routed.boundaryIntertwining
  refine
    { targetPairing := routed.targetPairing
      occurrenceCount := routed.occurrenceCount
      key := routed.key
      key_injective := routed.key_injective
      boundaryIntertwining := hboundary
      preservesTotalC := ?_
      seamDelta_false := ?_
      seamDelta_true := ?_
      fine := ?_
      twoCycle := ?_ }
  · unfold FKColoredStrandSplice.PreservesTotalC
      fkColoredSlotPairEqualCount
    simpa only [hcolor] using routed.preservesTotalC
  · unfold FKColoredStrandSplice.seamDelta
    rw [htarget, harrows false]
    exact routed.seamDelta_false
  · unfold FKColoredStrandSplice.seamDelta
    rw [htarget, harrows true]
    exact routed.seamDelta_true
  · change sixVertexHorizontalPairBoundedFineRowProfile
        ((rebasedSplice.target false).arrows.horizontal,
          (rebasedSplice.target true).arrows.horizontal) = _
    rw [htarget, harrows false, harrows true]
    exact certificate.fine
  · change sixVertexPairAtMostTwoCycleRelated
      ((rebased false).arrows, (rebased true).arrows)
      ((rebasedSplice.target false).arrows,
        (rebasedSplice.target true).arrows)
    rw [htarget, harrows false, harrows true]
    exact certificate.twoCycle


end
end StatMech.FrontierD
