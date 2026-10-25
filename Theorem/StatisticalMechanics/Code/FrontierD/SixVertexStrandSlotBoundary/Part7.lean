/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part7


namespace StatMech.FrontierD

noncomputable section

theorem coloredIndexedOccurrenceSlotIntertwining_of_successor
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (next : Fin n -> Fin n)
    (htarget : forall layer i,
      fkColoredStrandSlotBoundaryPerm (targetPairing layer)
          (key layer i) = key layer (next i))
    (hsource : forall layer i,
      fkColoredStrandSlotBoundaryPerm (source layer).pairing
          (key layer i) = key layer (next i))
    (hfixed : forall layer slot,
      (¬ exists i, key layer i = slot) ->
      fkColoredStrandSlotBoundaryPerm (targetPairing layer) slot =
          fkColoredStrandSlotBoundaryPerm (source layer).pairing slot /\
        (¬ exists i, key layer i =
          fkColoredStrandSlotBoundaryPerm (targetPairing layer) slot)) :
    FKColoredIndexedOccurrenceSlotIntertwining
      source targetPairing n key hinjective := by
  intro slot
  rcases slot with ⟨layer, slot⟩
  by_cases hselected : exists i, key layer i = slot
  · obtain ⟨i, rfl⟩ := hselected
    change fkIndexedOccurrenceSlotEquiv n key hinjective
        (layer, fkColoredStrandSlotBoundaryPerm
          (targetPairing layer) (key layer i)) =
      fkColoredLayeredStrandSlotBoundaryPerm
        (fun layer => (source layer).pairing)
        (fkIndexedOccurrenceSlotEquiv n key hinjective
          (layer, key layer i))
    rw [htarget,
      fkIndexedOccurrenceSlotEquiv_apply_key,
      fkIndexedOccurrenceSlotEquiv_apply_key]
    change (!layer, key (!layer) (next i)) =
      (!layer, fkColoredStrandSlotBoundaryPerm
        (source (!layer)).pairing (key (!layer) i))
    rw [hsource]
  · have hfix := hfixed layer slot hselected
    have houtput : ¬ exists i, key layer i =
        fkColoredStrandSlotBoundaryPerm (source layer).pairing slot := by
      rw [← hfix.1]
      exact hfix.2
    rw [fkColoredLayeredStrandSlotBoundaryPerm_apply,
      hfix.1,
      fkIndexedOccurrenceSlotEquiv_apply_of_not_routed
        n key hinjective (layer, slot)]
    · rw [fkColoredLayeredStrandSlotBoundaryPerm_apply,
      fkIndexedOccurrenceSlotEquiv_apply_of_not_routed
          n key hinjective]
      simpa using houtput
    · simpa using hselected

end
end StatMech.FrontierD
