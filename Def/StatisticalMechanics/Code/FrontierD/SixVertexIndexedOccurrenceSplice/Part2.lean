/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexIndexedOccurrenceSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice


namespace StatMech.FrontierD

noncomputable section

def FKColoredIndexedOccurrenceBoundaryIntertwining
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer)) : Prop :=
  forall x : FKLayeredMedialDart T,
    fkColoredStrandSpliceRawColor source targetPairing
        (fkIndexedOccurrenceSlotEquiv n key hinjective)
        (x.1, fkMedialBoundaryStep (targetPairing x.1) x.2) =
      fkColoredStrandSpliceRawColor source targetPairing
        (fkIndexedOccurrenceSlotEquiv n key hinjective) x


def FKColoredStrandSplice.ofIndexedOccurrences
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hboundary : FKColoredIndexedOccurrenceBoundaryIntertwining
      source targetPairing n key hinjective) :
    FKColoredStrandSplice source :=
  FKColoredStrandSplice.ofBoundaryInvariant source targetPairing
    (fkIndexedOccurrenceSlotEquiv n key hinjective) hboundary

end
end StatMech.FrontierD
