/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part6


namespace StatMech.FrontierD

noncomputable section

theorem fkColoredStrandSpliceRawColor_blackDart
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T)
    (layer : Bool) (dart : FKMedialBlackDart T) :
    fkColoredStrandSpliceRawColor source targetPairing slotEquiv
        (layer, dart.1) =
      fkColoredLayeredSlotColor source
        (slotEquiv (layer,
          fkColoredBlackDartStrandSlotEquiv
            (targetPairing layer) dart)) := by
  simp [fkColoredStrandSpliceRawColor,
    fkColoredBlackDartStrandSlotEquiv_apply,
    fkColoredBlackDartStrandSlot]


theorem fkColoredStrandSpliceRawColor_blackBoundary
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hintertwines : FKColoredIndexedOccurrenceSlotIntertwining
      source targetPairing n key hinjective)
    (layer : Bool) (dart : FKMedialBlackDart T) :
    fkColoredStrandSpliceRawColor source targetPairing
        (fkIndexedOccurrenceSlotEquiv n key hinjective)
        (layer, (fkMedialBlackBoundaryPerm
          (targetPairing layer) dart).1) =
      fkColoredStrandSpliceRawColor source targetPairing
        (fkIndexedOccurrenceSlotEquiv n key hinjective)
        (layer, dart.1) := by
  rw [fkColoredStrandSpliceRawColor_blackDart,
    fkColoredStrandSpliceRawColor_blackDart]
  let slot : FKLayeredStrandSlot T :=
    (layer, fkColoredBlackDartStrandSlotEquiv
      (targetPairing layer) dart)
  have hstep : fkColoredLayeredStrandSlotBoundaryPerm
      targetPairing slot =
      (layer, fkColoredBlackDartStrandSlotEquiv
        (targetPairing layer)
        (fkMedialBlackBoundaryPerm (targetPairing layer) dart)) := by
    change (layer, fkColoredBlackDartStrandSlotEquiv
        (targetPairing layer)
        (fkMedialBlackBoundaryPerm (targetPairing layer)
          ((fkColoredBlackDartStrandSlotEquiv
            (targetPairing layer)).symm
            (fkColoredBlackDartStrandSlotEquiv
              (targetPairing layer) dart)))) = _
    rw [(fkColoredBlackDartStrandSlotEquiv
      (targetPairing layer)).symm_apply_apply]
  rw [← hstep, hintertwines]
  exact fkColoredLayeredSlotColor_boundaryPerm source
    (fkIndexedOccurrenceSlotEquiv n key hinjective slot)


theorem fkColoredStrandSpliceRawColor_blackBoundary_of_slotColorInvariant
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hinvariant : FKColoredIndexedOccurrenceSlotColorInvariant
      source targetPairing n key hinjective)
    (layer : Bool) (dart : FKMedialBlackDart T) :
    fkColoredStrandSpliceRawColor source targetPairing
        (fkIndexedOccurrenceSlotEquiv n key hinjective)
        (layer, (fkMedialBlackBoundaryPerm
          (targetPairing layer) dart).1) =
      fkColoredStrandSpliceRawColor source targetPairing
        (fkIndexedOccurrenceSlotEquiv n key hinjective)
        (layer, dart.1) := by
  rw [fkColoredStrandSpliceRawColor_blackDart,
    fkColoredStrandSpliceRawColor_blackDart]
  let slot : FKLayeredStrandSlot T :=
    (layer, fkColoredBlackDartStrandSlotEquiv
      (targetPairing layer) dart)
  have hstep : fkColoredLayeredStrandSlotBoundaryPerm
      targetPairing slot =
      (layer, fkColoredBlackDartStrandSlotEquiv
        (targetPairing layer)
        (fkMedialBlackBoundaryPerm (targetPairing layer) dart)) := by
    change (layer, fkColoredBlackDartStrandSlotEquiv
        (targetPairing layer)
        (fkMedialBlackBoundaryPerm (targetPairing layer)
          ((fkColoredBlackDartStrandSlotEquiv
            (targetPairing layer)).symm
            (fkColoredBlackDartStrandSlotEquiv
              (targetPairing layer) dart)))) = _
    rw [(fkColoredBlackDartStrandSlotEquiv
      (targetPairing layer)).symm_apply_apply]
  rw [← hstep]
  exact hinvariant slot


theorem coloredIndexedOccurrenceBoundaryIntertwining_of_slot
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hintertwines : FKColoredIndexedOccurrenceSlotIntertwining
      source targetPairing n key hinjective) :
    FKColoredIndexedOccurrenceBoundaryIntertwining
      source targetPairing n key hinjective := by
  intro x
  rcases x with ⟨layer, dart⟩
  by_cases hblack : fkMedialCheckerColor dart = false
  · let blackDart : FKMedialBlackDart T := ⟨dart, hblack⟩
    simpa [blackDart, fkMedialBlackBoundaryPerm_val_step] using
      fkColoredStrandSpliceRawColor_blackBoundary source targetPairing
        n key hinjective hintertwines layer blackDart
  · have hwhite : fkMedialCheckerColor dart = true := by
      cases h : fkMedialCheckerColor dart <;> simp_all
    let boundary := fkMedialBoundaryStep (targetPairing layer) dart
    have hboundaryWhite : fkMedialCheckerColor boundary = true := by
      simpa [boundary, hwhite] using
        fkMedialCheckerColor_boundaryStep (targetPairing layer) dart
    have hpreBlack : fkMedialCheckerColor
        (fkMedialLocalMate (targetPairing layer) boundary) = false := by
      have hne := fkMedialCheckerColor_localMate_ne
        (targetPairing layer) boundary
      cases h : fkMedialCheckerColor
          (fkMedialLocalMate (targetPairing layer) boundary) <;>
        simp_all
    let predecessor : FKMedialBlackDart T :=
      ⟨fkMedialLocalMate (targetPairing layer) boundary, hpreBlack⟩
    have hnext : fkMedialBlackBoundaryPerm
        (targetPairing layer) predecessor =
      (⟨fkMedialLocalMate (targetPairing layer) dart, by
        have hne := fkMedialCheckerColor_localMate_ne
          (targetPairing layer) dart
        cases h : fkMedialCheckerColor
            (fkMedialLocalMate (targetPairing layer) dart) <;>
          simp_all⟩ : FKMedialBlackDart T) := by
      apply Subtype.ext
      simp [predecessor, boundary, fkMedialBoundaryStep_apply,
        fkMedialLocalMate_involutive,
        fkMedialBondMate_involutive]
    have hroute := fkColoredStrandSpliceRawColor_blackBoundary
      source targetPairing n key hinjective hintertwines layer predecessor
    rw [hnext] at hroute
    have hlocalDart := fkColoredStrandSpliceRawColor_localMate
      source targetPairing
      (fkIndexedOccurrenceSlotEquiv n key hinjective) layer dart
    have hlocalBoundary := fkColoredStrandSpliceRawColor_localMate
      source targetPairing
      (fkIndexedOccurrenceSlotEquiv n key hinjective) layer boundary
    exact hlocalBoundary.symm.trans (hroute.symm.trans hlocalDart)


theorem coloredIndexedOccurrenceBoundaryIntertwining_of_slotColorInvariant
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hinvariant : FKColoredIndexedOccurrenceSlotColorInvariant
      source targetPairing n key hinjective) :
    FKColoredIndexedOccurrenceBoundaryIntertwining
      source targetPairing n key hinjective := by
  intro x
  rcases x with ⟨layer, dart⟩
  by_cases hblack : fkMedialCheckerColor dart = false
  · let blackDart : FKMedialBlackDart T := ⟨dart, hblack⟩
    simpa [blackDart, fkMedialBlackBoundaryPerm_val_step] using
      fkColoredStrandSpliceRawColor_blackBoundary_of_slotColorInvariant
        source targetPairing n key hinjective hinvariant layer blackDart
  · have hwhite : fkMedialCheckerColor dart = true := by
      cases h : fkMedialCheckerColor dart <;> simp_all
    let boundary := fkMedialBoundaryStep (targetPairing layer) dart
    have hboundaryWhite : fkMedialCheckerColor boundary = true := by
      simpa [boundary, hwhite] using
        fkMedialCheckerColor_boundaryStep (targetPairing layer) dart
    have hpreBlack : fkMedialCheckerColor
        (fkMedialLocalMate (targetPairing layer) boundary) = false := by
      have hne := fkMedialCheckerColor_localMate_ne
        (targetPairing layer) boundary
      cases h : fkMedialCheckerColor
          (fkMedialLocalMate (targetPairing layer) boundary) <;>
        simp_all
    let predecessor : FKMedialBlackDart T :=
      ⟨fkMedialLocalMate (targetPairing layer) boundary, hpreBlack⟩
    have hnext : fkMedialBlackBoundaryPerm
        (targetPairing layer) predecessor =
      (⟨fkMedialLocalMate (targetPairing layer) dart, by
        have hne := fkMedialCheckerColor_localMate_ne
          (targetPairing layer) dart
        cases h : fkMedialCheckerColor
            (fkMedialLocalMate (targetPairing layer) dart) <;>
          simp_all⟩ : FKMedialBlackDart T) := by
      apply Subtype.ext
      simp [predecessor, boundary, fkMedialBoundaryStep_apply,
        fkMedialLocalMate_involutive,
        fkMedialBondMate_involutive]
    have hroute :=
      fkColoredStrandSpliceRawColor_blackBoundary_of_slotColorInvariant
        source targetPairing n key hinjective hinvariant layer predecessor
    rw [hnext] at hroute
    have hlocalDart := fkColoredStrandSpliceRawColor_localMate
      source targetPairing
      (fkIndexedOccurrenceSlotEquiv n key hinjective) layer dart
    have hlocalBoundary := fkColoredStrandSpliceRawColor_localMate
      source targetPairing
      (fkIndexedOccurrenceSlotEquiv n key hinjective) layer boundary
    exact hlocalBoundary.symm.trans (hroute.symm.trans hlocalDart)


end
end StatMech.FrontierD
