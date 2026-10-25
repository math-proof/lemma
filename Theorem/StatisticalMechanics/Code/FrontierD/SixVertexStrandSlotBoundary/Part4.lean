/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part4


namespace StatMech.FrontierD

noncomputable section

theorem fkColoredStrandSlotBoundaryPerm_toggle
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (v : T.Vertex) :
    fkColoredStrandSlotBoundaryPerm
        (fkMedialTogglePairingAt pairing v) =
      if fkMedialVertexParity v = true then
        (fkColoredStrandSlotBoundaryPerm pairing).trans
          (fkColoredVertexStrandSlotSwap v)
      else
        (fkColoredVertexStrandSlotSwap v).trans
          (fkColoredStrandSlotBoundaryPerm pairing) := by
  apply Equiv.ext
  intro slot
  by_cases hv : fkMedialVertexParity v = true
  · rw [if_pos hv]
    have hcoordinate :
        fkColoredBlackDartStrandSlotEquiv
            (fkMedialTogglePairingAt pairing v) =
          (fkColoredBlackDartStrandSlotEquiv pairing).trans
            (fkColoredVertexStrandSlotSwap v) := by
      rw [fkColoredBlackDartStrandSlotEquiv_toggle, if_pos hv]
    simp only [fkColoredStrandSlotBoundaryPerm, Equiv.trans_apply]
    rw [fkMedialBlackBoundaryPerm_toggle, hcoordinate]
    simp only [Equiv.trans_apply, Equiv.Perm.mul_apply]
    have hcancel : fkMedialBlackDartSwap v
        (((fkColoredBlackDartStrandSlotEquiv pairing).trans
          (fkColoredVertexStrandSlotSwap v)).symm slot) =
        (fkColoredBlackDartStrandSlotEquiv pairing).symm slot := by
      apply (fkColoredBlackDartStrandSlotEquiv pairing).injective
      rw [fkColoredBlackDartStrandSlot_blackSwap]
      simp
    rw [hcancel]
  · rw [if_neg hv]
    have hcoordinate :
        fkColoredBlackDartStrandSlotEquiv
            (fkMedialTogglePairingAt pairing v) =
          fkColoredBlackDartStrandSlotEquiv pairing := by
      rw [fkColoredBlackDartStrandSlotEquiv_toggle, if_neg hv]
    simp only [fkColoredStrandSlotBoundaryPerm, Equiv.trans_apply]
    rw [fkMedialBlackBoundaryPerm_toggle, hcoordinate]
    simp only [Equiv.Perm.mul_apply]
    have hinput : fkMedialBlackDartSwap v
        ((fkColoredBlackDartStrandSlotEquiv pairing).symm slot) =
        (fkColoredBlackDartStrandSlotEquiv pairing).symm
          (fkColoredVertexStrandSlotSwap v slot) := by
      apply (fkColoredBlackDartStrandSlotEquiv pairing).injective
      rw [fkColoredBlackDartStrandSlot_blackSwap]
      simp
    rw [hinput]

theorem FKColoredLoopPairing.color_blackDart_eq_slotColor
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (layer : Bool) (dart : FKMedialBlackDart T) :
    (source layer).color dart.1 =
      fkColoredLayeredSlotColor source
        (layer, fkColoredBlackDartStrandSlotEquiv
          (source layer).pairing dart) := by
  simpa [fkColoredBlackDartStrandSlotEquiv_apply,
    fkColoredBlackDartStrandSlot] using
      FKColoredLoopPairing.color_eq_slotColor source
        layer dart.1.1 dart.1.2


theorem FKColoredLoopPairing.slotColor_boundaryPerm
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (layer : Bool) (slot : T.Vertex × Bool) :
    fkColoredLayeredSlotColor source
        (layer, fkColoredStrandSlotBoundaryPerm
          (source layer).pairing slot) =
      fkColoredLayeredSlotColor source (layer, slot) := by
  let coordinate := fkColoredBlackDartStrandSlotEquiv
    (source layer).pairing
  let dart := coordinate.symm slot
  have hdart : coordinate dart = slot := coordinate.apply_symm_apply slot
  have hboundary :
      (source layer).color
          (fkMedialBlackBoundaryPerm (source layer).pairing dart).1 =
        (source layer).color dart.1 := by
    exact ((source layer).color_bondMate
      (fkMedialLocalMate (source layer).pairing dart.1)).trans
        ((source layer).color_localMate dart.1)
  change fkColoredLayeredSlotColor source
      (layer, coordinate
        (fkMedialBlackBoundaryPerm (source layer).pairing dart)) =
    fkColoredLayeredSlotColor source (layer, slot)
  rw [← hdart]
  rw [← FKColoredLoopPairing.color_blackDart_eq_slotColor
      source layer,
    ← FKColoredLoopPairing.color_blackDart_eq_slotColor source layer]
  exact hboundary


end
end StatMech.FrontierD
