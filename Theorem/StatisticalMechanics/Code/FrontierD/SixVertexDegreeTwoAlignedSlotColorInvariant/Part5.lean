/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTransitionRetieExact.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySlotColorInvariant.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalUnitRoute.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part5


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkColoredParityMaskStrandSlotSwap_self
    {T : EvenTorus} (mask : T.Vertex -> Bool) (parity : Bool)
    (slot : T.Vertex × Bool) :
    fkColoredParityMaskStrandSlotSwap mask parity
        (fkColoredParityMaskStrandSlotSwap mask parity slot) = slot := by
  rcases slot with ⟨v, side⟩
  cases hmask : mask v <;> cases hv : fkMedialVertexParity v <;>
    cases parity <;> cases side <;>
    simp [fkColoredParityMaskStrandSlotSwap, hmask, hv]

theorem fkColoredParityMaskStrandSlotSwap_apply_of_true
    {T : EvenTorus} (mask : T.Vertex -> Bool) (parity : Bool)
    (slot : T.Vertex × Bool)
    (hselected : (mask slot.1 &&
      (fkMedialVertexParity slot.1 == parity)) = true) :
    fkColoredParityMaskStrandSlotSwap mask parity slot =
      fkColoredVertexStrandSlotSwap slot.1 slot := by
  rcases slot with ⟨v, side⟩
  cases hmask : mask v <;> cases hv : fkMedialVertexParity v <;>
    cases parity <;> cases side <;>
    simp [fkColoredParityMaskStrandSlotSwap,
      fkColoredVertexStrandSlotSwap, hmask, hv] at hselected ⊢

theorem fkColoredParityMaskStrandSlotSwap_apply_of_false
    {T : EvenTorus} (mask : T.Vertex -> Bool) (parity : Bool)
    (slot : T.Vertex × Bool)
    (hunselected : (mask slot.1 &&
      (fkMedialVertexParity slot.1 == parity)) = false) :
    fkColoredParityMaskStrandSlotSwap mask parity slot = slot := by
  rcases slot with ⟨v, side⟩
  cases hmask : mask v <;> cases hv : fkMedialVertexParity v <;>
    cases parity <;> cases side <;>
    simp [fkColoredParityMaskStrandSlotSwap, hmask, hv] at hunselected ⊢


theorem fkMedialBlackBoundaryPerm_togglePairingMask
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (mask : T.Vertex -> Bool) :
    fkMedialBlackBoundaryPerm (fkMedialTogglePairingMask pairing mask) =
      fkMedialBlackBoundaryPerm pairing * fkMedialBlackDartMaskSwap mask := by
  apply Equiv.ext
  intro dart
  apply Subtype.ext
  rcases dart with ⟨⟨v, side⟩, hdart⟩
  cases hmask : mask v <;> cases hp : pairing v <;>
    cases hv : fkMedialVertexParity v <;> cases side <;>
    simp [fkMedialBlackBoundaryPerm_val, fkMedialTogglePairingMask,
      fkMedialBlackDartMaskSwap, fkMedialBlackDartSwap,
      fkMedialBlackDart0, fkMedialBlackDart1, fkMedialCheckerColor,
      fkMedialSideVertical, fkMedialLocalMate, Equiv.Perm.mul_apply,
      hmask, hp, hv] at hdart ⊢


theorem fkColoredBlackDartStrandSlotEquiv_togglePairingMask
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (mask : T.Vertex -> Bool) :
    fkColoredBlackDartStrandSlotEquiv
        (fkMedialTogglePairingMask pairing mask) =
      (fkColoredBlackDartStrandSlotEquiv pairing).trans
        (fkColoredParityMaskStrandSlotSwap mask true) := by
  apply Equiv.ext
  intro dart
  rcases dart with ⟨⟨v, side⟩, hdart⟩
  cases hmask : mask v <;> cases hp : pairing v <;>
    cases hv : fkMedialVertexParity v <;> cases side <;>
    simp [fkColoredBlackDartStrandSlotEquiv_apply,
      fkColoredBlackDartStrandSlot, fkMedialTogglePairingMask,
      fkColoredParityMaskStrandSlotSwap, fkColoredSideSlot,
      fkMedialCheckerColor, fkMedialSideVertical, hmask, hp, hv] at hdart ⊢


theorem fkColoredBlackDartStrandSlotEquiv_blackDartMaskSwap
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (mask : T.Vertex -> Bool) (dart : FKMedialBlackDart T) :
    fkColoredBlackDartStrandSlotEquiv pairing
        (fkMedialBlackDartMaskSwap mask dart) =
      fkColoredParityMaskStrandSlotSwap mask false
        (fkColoredParityMaskStrandSlotSwap mask true
          (fkColoredBlackDartStrandSlotEquiv pairing dart)) := by
  rcases dart with ⟨⟨v, side⟩, hdart⟩
  cases hmask : mask v <;> cases hp : pairing v <;>
    cases hv : fkMedialVertexParity v <;> cases side <;>
    simp [fkMedialBlackDartMaskSwap, fkMedialBlackDartSwap,
      fkMedialBlackDart0, fkMedialBlackDart1,
      fkColoredBlackDartStrandSlotEquiv_apply,
      fkColoredBlackDartStrandSlot, fkColoredParityMaskStrandSlotSwap,
      fkColoredSideSlot, fkMedialCheckerColor, fkMedialSideVertical,
      hmask, hp, hv] at hdart ⊢


theorem fkColoredStrandSlotBoundaryPerm_togglePairingMask
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (mask : T.Vertex -> Bool) :
    fkColoredStrandSlotBoundaryPerm
        (fkMedialTogglePairingMask pairing mask) =
      (fkColoredParityMaskStrandSlotSwap mask false).trans
        ((fkColoredStrandSlotBoundaryPerm pairing).trans
          (fkColoredParityMaskStrandSlotSwap mask true)) := by
  let coordinate := fkColoredBlackDartStrandSlotEquiv pairing
  let whiteSwap := fkColoredParityMaskStrandSlotSwap mask false
  let blackSwap := fkColoredParityMaskStrandSlotSwap mask true
  have htargetCoordinate :=
    fkColoredBlackDartStrandSlotEquiv_togglePairingMask pairing mask
  have htargetBoundary := fkMedialBlackBoundaryPerm_togglePairingMask
    pairing mask
  apply Equiv.ext
  intro slot
  have hinput : fkMedialBlackDartMaskSwap mask
      (coordinate.symm (blackSwap slot)) =
      coordinate.symm (whiteSwap slot) := by
    apply coordinate.injective
    rw [fkColoredBlackDartStrandSlotEquiv_blackDartMaskSwap]
    simp [coordinate, whiteSwap, blackSwap]
  simp only [fkColoredStrandSlotBoundaryPerm, Equiv.trans_apply]
  rw [htargetCoordinate, htargetBoundary]
  simp only [Equiv.trans_apply, Equiv.Perm.mul_apply]
  rw [show ((coordinate.trans blackSwap).symm slot) =
      coordinate.symm (blackSwap slot) by
    change coordinate.symm (blackSwap.symm slot) = _
    rw [show blackSwap.symm slot = blackSwap slot by rfl]]
  rw [hinput]

@[simp] theorem fkMedialTogglePairingMask_self
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (mask : T.Vertex -> Bool) :
    fkMedialTogglePairingMask
        (fkMedialTogglePairingMask pairing mask) mask = pairing := by
  funext v
  cases hmask : mask v <;> simp [fkMedialTogglePairingMask, hmask]


end
end StatMech.FrontierD
