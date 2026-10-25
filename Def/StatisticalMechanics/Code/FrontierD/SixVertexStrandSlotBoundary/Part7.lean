/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part6


namespace StatMech.FrontierD

noncomputable section

def FKColoredStrandSplice.ofIndexedSlotIntertwining
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hintertwines : FKColoredIndexedOccurrenceSlotIntertwining
      source targetPairing n key hinjective) :
    FKColoredStrandSplice source :=
  FKColoredStrandSplice.ofIndexedOccurrences source targetPairing
    n key hinjective
      (coloredIndexedOccurrenceBoundaryIntertwining_of_slot
        source targetPairing n key hinjective hintertwines)


end
end StatMech.FrontierD
