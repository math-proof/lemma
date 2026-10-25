/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedKeySlotColorInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part7


namespace StatMech.FrontierD

noncomputable section

def fkColoredSlotColorInvariantSplice
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hinvariant : FKColoredIndexedOccurrenceSlotColorInvariant
      source targetPairing n key hinjective) :
    FKColoredStrandSplice source :=
  FKColoredStrandSplice.ofIndexedOccurrences source targetPairing n key
    hinjective
    (coloredIndexedOccurrenceBoundaryIntertwining_of_slotColorInvariant
      source targetPairing n key hinjective hinvariant)


def FKColoredUnitTransferRoutedKey.ofSlotColorInvariant
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
      key hinjective hinvariant).seamDelta true = -1) :
    FKColoredUnitTransferRoutedKey source :=
  { targetPairing := targetPairing
    occurrenceCount := n
    key := key
    key_injective := hinjective
    boundaryIntertwining :=
      coloredIndexedOccurrenceBoundaryIntertwining_of_slotColorInvariant
        source targetPairing n key hinjective hinvariant
    preservesTotalC := hTotalC
    seamDelta_false := hfalse
    seamDelta_true := htrue }

end
end StatMech.FrontierD
