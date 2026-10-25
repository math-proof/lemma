/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part5


namespace StatMech.FrontierD

noncomputable section

def FKColoredIndexedOccurrenceSlotIntertwining
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer)) : Prop :=
  forall slot : FKLayeredStrandSlot T,
    fkIndexedOccurrenceSlotEquiv n key hinjective
        (fkColoredLayeredStrandSlotBoundaryPerm targetPairing slot) =
      fkColoredLayeredStrandSlotBoundaryPerm
        (fun layer => (source layer).pairing)
        (fkIndexedOccurrenceSlotEquiv n key hinjective slot)


def FKColoredIndexedOccurrenceSlotColorInvariant
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer)) : Prop :=
  forall slot : FKLayeredStrandSlot T,
    fkColoredLayeredSlotColor source
        (fkIndexedOccurrenceSlotEquiv n key hinjective
          (fkColoredLayeredStrandSlotBoundaryPerm targetPairing slot)) =
      fkColoredLayeredSlotColor source
        (fkIndexedOccurrenceSlotEquiv n key hinjective slot)


end
end StatMech.FrontierD
