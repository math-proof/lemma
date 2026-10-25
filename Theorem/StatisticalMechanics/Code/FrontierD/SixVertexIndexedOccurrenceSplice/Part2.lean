/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexIndexedOccurrenceSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part11
import Def.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice.Part2


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem FKColoredStrandSplice.ofIndexedOccurrences_slotEquiv
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hboundary : FKColoredIndexedOccurrenceBoundaryIntertwining
      source targetPairing n key hinjective) :
    (FKColoredStrandSplice.ofIndexedOccurrences source targetPairing
      n key hinjective hboundary).slotEquiv =
        fkIndexedOccurrenceSlotEquiv n key hinjective := rfl


theorem FKColoredStrandSplice.ofIndexedOccurrences_recover
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hboundary : FKColoredIndexedOccurrenceBoundaryIntertwining
      source targetPairing n key hinjective) :
    (FKColoredStrandSplice.ofIndexedOccurrences source targetPairing
      n key hinjective hboundary).symm.target = source :=
  FKColoredStrandSplice.symm_target _


theorem FKColoredStrandSplice.target_bigrade
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source)
    (hC : splice.PreservesTotalC) :
    (fkColoredLoopPairingPairTotalC splice.target,
        fkColoredTrueStrandSlotCount splice.target) =
      (fkColoredLoopPairingPairTotalC source,
        fkColoredTrueStrandSlotCount source) := by
  apply Prod.ext
  · exact splice.target_totalC hC
  · exact splice.target_trueStrandSlotCount

end
end StatMech.FrontierD
