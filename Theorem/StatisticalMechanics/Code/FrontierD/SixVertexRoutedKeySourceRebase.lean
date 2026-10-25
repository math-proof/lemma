/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedKeySourceRebase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySlotColorInvariant.Part2


namespace StatMech.FrontierD

noncomputable section

theorem coloredIndexedOccurrenceBoundaryIntertwining_rebase
    {T : EvenTorus} (source rebased : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hcolor : forall slot : FKLayeredStrandSlot T,
      fkColoredLayeredSlotColor rebased slot =
        fkColoredLayeredSlotColor source slot)
    (hboundary : FKColoredIndexedOccurrenceBoundaryIntertwining
      source targetPairing n key hinjective) :
    FKColoredIndexedOccurrenceBoundaryIntertwining
      rebased targetPairing n key hinjective := by
  intro x
  simpa only [fkColoredStrandSpliceRawColor, hcolor] using hboundary x


theorem indexedOccurrenceSplice_target_rebase
    {T : EvenTorus} (source rebased : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hcolor : forall slot : FKLayeredStrandSlot T,
      fkColoredLayeredSlotColor rebased slot =
        fkColoredLayeredSlotColor source slot)
    (hboundary : FKColoredIndexedOccurrenceBoundaryIntertwining
      source targetPairing n key hinjective) :
    (FKColoredStrandSplice.ofIndexedOccurrences rebased targetPairing n key
        hinjective
        (coloredIndexedOccurrenceBoundaryIntertwining_rebase source rebased
          targetPairing n key hinjective hcolor hboundary)).target =
      (FKColoredStrandSplice.ofIndexedOccurrences source targetPairing n key
        hinjective hboundary).target := by
  funext layer
  apply FKColoredLoopPairing.ext
  · rfl
  · funext dart
    change fkColoredStrandSpliceRawColor rebased targetPairing
        (fkIndexedOccurrenceSlotEquiv n key hinjective) (layer, dart) =
      fkColoredStrandSpliceRawColor source targetPairing
        (fkIndexedOccurrenceSlotEquiv n key hinjective) (layer, dart)
    simp only [fkColoredStrandSpliceRawColor, hcolor]


end
end StatMech.FrontierD
