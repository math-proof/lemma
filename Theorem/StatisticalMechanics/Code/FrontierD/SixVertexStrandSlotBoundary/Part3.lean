/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part3


namespace StatMech.FrontierD

noncomputable section

theorem fkColoredBlackDartStrandSlot_toggle
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (v : T.Vertex) (dart : FKMedialBlackDart T) :
    fkColoredBlackDartStrandSlot
        (fkMedialTogglePairingAt pairing v) dart =
      if fkMedialVertexParity v = true then
        fkColoredVertexStrandSlotSwap v
          (fkColoredBlackDartStrandSlot pairing dart)
      else fkColoredBlackDartStrandSlot pairing dart := by
  rcases dart with ⟨⟨w, side⟩, hdart⟩
  by_cases hw : w = v
  · subst w
    cases hp : pairing v <;> cases hv : fkMedialVertexParity v <;>
      cases side <;>
      simp [fkColoredBlackDartStrandSlot,
        fkColoredVertexStrandSlotSwap, fkColoredSideSlot,
        fkMedialTogglePairingAt, hp, fkMedialCheckerColor,
        fkMedialSideVertical, hv] at hdart ⊢
  · have hfalse :
        (w, fkColoredSideSlot (pairing w) side) ≠ (v, false) := by
      intro h
      exact hw (congrArg Prod.fst h)
    have htrue :
        (w, fkColoredSideSlot (pairing w) side) ≠ (v, true) := by
      intro h
      exact hw (congrArg Prod.fst h)
    simp [fkColoredBlackDartStrandSlot,
      fkColoredVertexStrandSlotSwap, fkMedialTogglePairingAt, hw,
      Equiv.swap_apply_of_ne_of_ne hfalse htrue]

theorem fkColoredBlackDartStrandSlotEquiv_toggle
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (v : T.Vertex) :
    fkColoredBlackDartStrandSlotEquiv
        (fkMedialTogglePairingAt pairing v) =
      if fkMedialVertexParity v = true then
        (fkColoredBlackDartStrandSlotEquiv pairing).trans
          (fkColoredVertexStrandSlotSwap v)
      else fkColoredBlackDartStrandSlotEquiv pairing := by
  apply Equiv.ext
  intro dart
  rw [fkColoredBlackDartStrandSlotEquiv_apply]
  by_cases hv : fkMedialVertexParity v = true
  · rw [if_pos hv]
    simp only [Equiv.trans_apply,
      fkColoredBlackDartStrandSlotEquiv_apply]
    simpa [hv] using
      fkColoredBlackDartStrandSlot_toggle pairing v dart
  · rw [if_neg hv]
    simpa [hv] using
      fkColoredBlackDartStrandSlot_toggle pairing v dart

theorem fkColoredBlackDartStrandSlot_blackSwap
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (v : T.Vertex) (dart : FKMedialBlackDart T) :
    fkColoredBlackDartStrandSlotEquiv pairing
        (fkMedialBlackDartSwap v dart) =
      fkColoredVertexStrandSlotSwap v
        (fkColoredBlackDartStrandSlotEquiv pairing dart) := by
  rcases dart with ⟨⟨w, side⟩, hdart⟩
  by_cases hw : w = v
  · subst w
    cases hp : pairing v <;> cases hv : fkMedialVertexParity v <;>
      cases side <;>
      simp [fkColoredBlackDartStrandSlotEquiv_apply,
        fkColoredBlackDartStrandSlot, fkMedialBlackDartSwap,
        fkMedialBlackDart0, fkMedialBlackDart1,
        fkColoredVertexStrandSlotSwap, fkColoredSideSlot,
        fkMedialCheckerColor, fkMedialSideVertical, hp, hv] at hdart ⊢
  · have hzero : (⟨⟨w, side⟩, hdart⟩ : FKMedialBlackDart T) ≠
        fkMedialBlackDart0 v := by
      intro h
      exact hw (congrArg (fun d : FKMedialBlackDart T => d.1.1) h)
    have hone : (⟨⟨w, side⟩, hdart⟩ : FKMedialBlackDart T) ≠
        fkMedialBlackDart1 v := by
      intro h
      exact hw (congrArg (fun d : FKMedialBlackDart T => d.1.1) h)
    have hfalse :
        (w, fkColoredSideSlot (pairing w) side) ≠ (v, false) := by
      intro h
      exact hw (congrArg Prod.fst h)
    have htrue :
        (w, fkColoredSideSlot (pairing w) side) ≠ (v, true) := by
      intro h
      exact hw (congrArg Prod.fst h)
    simp [fkColoredBlackDartStrandSlotEquiv_apply,
      fkColoredBlackDartStrandSlot, fkMedialBlackDartSwap,
      fkColoredVertexStrandSlotSwap,
      Equiv.swap_apply_of_ne_of_ne hzero hone,
      Equiv.swap_apply_of_ne_of_ne hfalse htrue]


end
end StatMech.FrontierD
