/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedCrossRoutedKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexResolvedCrossRoutedKey


namespace StatMech.FrontierD

noncomputable section

theorem fkColoredVertexCrossOccurrenceKey_injective
    {T : EvenTorus} (mask : T.Vertex -> Bool) (layer : Bool) :
    Function.Injective (fkColoredVertexCrossOccurrenceKey mask layer) := by
  intro first second heq
  apply (Fintype.equivFin
    (FKColoredVertexCrossOccurrence mask)).symm.injective
  apply Subtype.ext
  exact heq

theorem fkColoredVertexCrossOccurrenceKey_exists_iff
    {T : EvenTorus} (mask : T.Vertex -> Bool) (layer : Bool)
    (slot : T.Vertex × Bool) :
    (exists i, fkColoredVertexCrossOccurrenceKey mask layer i = slot) ↔
      mask slot.1 = true := by
  constructor
  · rintro ⟨i, hi⟩
    let occurrence :=
      (Fintype.equivFin (FKColoredVertexCrossOccurrence mask)).symm i
    have hselected := occurrence.2
    change mask occurrence.1.1 = true at hselected
    have hoccurrence : occurrence.1 = slot := by
      change fkColoredVertexCrossOccurrenceKey mask layer i = slot
      exact hi
    rwa [hoccurrence] at hselected
  · intro hselected
    let occurrence : FKColoredVertexCrossOccurrence mask :=
      ⟨slot, hselected⟩
    let i := Fintype.equivFin
      (FKColoredVertexCrossOccurrence mask) occurrence
    refine ⟨i, ?_⟩
    change ((Fintype.equivFin
      (FKColoredVertexCrossOccurrence mask)).symm i).1 = slot
    rw [show (Fintype.equivFin
      (FKColoredVertexCrossOccurrence mask)).symm i = occurrence by
        simp [i]]

theorem fkIndexedOccurrenceSlotEquiv_vertexCross_eq
    {T : EvenTorus} (mask : T.Vertex -> Bool) :
    fkIndexedOccurrenceSlotEquiv
        (Fintype.card (FKColoredVertexCrossOccurrence mask))
        (fkColoredVertexCrossOccurrenceKey mask)
        (fkColoredVertexCrossOccurrenceKey_injective mask) =
      fkColoredFullSwapLayeredSlotEquiv mask := by
  apply Equiv.ext
  rintro ⟨layer, v, side⟩
  by_cases hm : mask v = true
  · let occurrence : FKColoredVertexCrossOccurrence mask :=
      ⟨(v, side), hm⟩
    let i := Fintype.equivFin
      (FKColoredVertexCrossOccurrence mask) occurrence
    have hkey : fkColoredVertexCrossOccurrenceKey mask layer i =
        (v, side) := by
      change ((Fintype.equivFin
        (FKColoredVertexCrossOccurrence mask)).symm i).1 = (v, side)
      rw [show (Fintype.equivFin
        (FKColoredVertexCrossOccurrence mask)).symm i = occurrence by
          simp [i]]
    rw [← hkey, fkIndexedOccurrenceSlotEquiv_apply_key]
    have hkey' : fkColoredVertexCrossOccurrenceKey mask (!layer) i =
        (v, side) := by
      change ((Fintype.equivFin
        (FKColoredVertexCrossOccurrence mask)).symm i).1 = (v, side)
      rw [show (Fintype.equivFin
        (FKColoredVertexCrossOccurrence mask)).symm i = occurrence by
          simp [i]]
    simp [fkColoredFullSwapLayeredSlotEquiv, hkey']
    exact ⟨by rw [hkey]; exact hm, hkey.symm⟩
  · have hnot : ¬ exists i,
        fkColoredVertexCrossOccurrenceKey mask layer i = (v, side) := by
      rw [fkColoredVertexCrossOccurrenceKey_exists_iff]
      exact hm
    rw [fkIndexedOccurrenceSlotEquiv_apply_of_not_routed _ _ _ _ hnot]
    simp [fkColoredFullSwapLayeredSlotEquiv, hm]

theorem fkColoredVertexCrossTarget_slotColorEquiv
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (cross : FKColoredResolvedUnitCross source) :
    FKColoredStrandSlotColorEquiv source cross.target
      (fkColoredFullSwapLayeredSlotEquiv cross.mask) := by
  intro slot
  exact (fkColoredVertexCrossTarget_slotColor source cross.mask
    cross.bondCoherent slot).symm


theorem FKColoredResolvedUnitCross.boundaryIntertwining
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (cross : FKColoredResolvedUnitCross source) :
    FKColoredIndexedOccurrenceBoundaryIntertwining source
      (fun layer => (source layer).pairing)
      (Fintype.card (FKColoredVertexCrossOccurrence cross.mask))
      (fkColoredVertexCrossOccurrenceKey cross.mask)
      (fkColoredVertexCrossOccurrenceKey_injective cross.mask) := by
  let slotEquiv := fkColoredFullSwapLayeredSlotEquiv cross.mask
  let colorSplice := FKColoredStrandSplice.ofColorEquiv source cross.target
    slotEquiv (fkColoredVertexCrossTarget_slotColorEquiv source cross)
  have hboundary :=
    (fkColoredStrandSpliceBondCoherent_iff_boundaryInvariant source
      (fun layer => (source layer).pairing) slotEquiv).1
      colorSplice.bondCoherent
  intro x
  rw [fkIndexedOccurrenceSlotEquiv_vertexCross_eq]
  exact hboundary x


theorem FKColoredResolvedUnitCross.indexedSplice_target
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (cross : FKColoredResolvedUnitCross source) :
    (FKColoredStrandSplice.ofIndexedOccurrences source
      (fun layer => (source layer).pairing)
      (Fintype.card (FKColoredVertexCrossOccurrence cross.mask))
      (fkColoredVertexCrossOccurrenceKey cross.mask)
      (fkColoredVertexCrossOccurrenceKey_injective cross.mask)
      cross.boundaryIntertwining).target = cross.target := by
  let indexed := FKColoredStrandSplice.ofIndexedOccurrences source
    (fun layer => (source layer).pairing)
    (Fintype.card (FKColoredVertexCrossOccurrence cross.mask))
    (fkColoredVertexCrossOccurrenceKey cross.mask)
    (fkColoredVertexCrossOccurrenceKey_injective cross.mask)
    cross.boundaryIntertwining
  funext layer
  apply FKColoredLoopPairing.ext
  · rfl
  · funext d
    have hslot := fkIndexedOccurrenceSlotEquiv_vertexCross_eq cross.mask
    change fkColoredStrandSpliceRawColor source
        (fun layer => (source layer).pairing) indexed.slotEquiv (layer, d) =
      (cross.target layer).color d
    rw [show indexed.slotEquiv =
        fkColoredFullSwapLayeredSlotEquiv cross.mask by
      exact hslot]
    exact fkColoredStrandSpliceRawColor_eq_of_colorEquiv source cross.target
      (fkColoredFullSwapLayeredSlotEquiv cross.mask)
      (fkColoredVertexCrossTarget_slotColorEquiv source cross) (layer, d)


end
end StatMech.FrontierD
