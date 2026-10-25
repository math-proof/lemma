/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part7
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem FKColoredStrandSplice.ofColorEquiv_target
    {T : EvenTorus} (source target : FKColoredLoopPairingPair T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T)
    (hcolor : FKColoredStrandSlotColorEquiv source target slotEquiv) :
    (FKColoredStrandSplice.ofColorEquiv
      source target slotEquiv hcolor).target = target := by
  funext layer
  apply FKColoredLoopPairing.ext
  · rfl
  · funext d
    exact fkColoredStrandSpliceRawColor_eq_of_colorEquiv
      source target slotEquiv hcolor (layer, d)

theorem FKColoredStrandSplice.target_slotColor
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source)
    (slot : FKLayeredStrandSlot T) :
    fkColoredLayeredSlotColor splice.target slot =
      fkColoredLayeredSlotColor source (splice.slotEquiv slot) := by
  rcases slot with ⟨layer, v, slot⟩
  cases slot <;>
    simp [fkColoredLayeredSlotColor, FKColoredStrandSplice.target,
      fkColoredStrandSpliceRawColor]


theorem FKColoredStrandSplice.target_trueStrandSlotCount
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source) :
    fkColoredTrueStrandSlotCount splice.target =
      fkColoredTrueStrandSlotCount source := by
  unfold fkColoredTrueStrandSlotCount
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv splice.slotEquiv
  intro slot
  rw [splice.target_slotColor]

theorem FKColoredStrandSplice.symm_rawColor
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source)
    (x : FKLayeredMedialDart T) :
    fkColoredStrandSpliceRawColor splice.target
        (fun layer => (source layer).pairing) splice.slotEquiv.symm x =
      (source x.1).color x.2 := by
  rcases x with ⟨layer, v, side⟩
  unfold fkColoredStrandSpliceRawColor
  rw [splice.target_slotColor]
  rw [splice.slotEquiv.apply_symm_apply]
  exact (FKColoredLoopPairing.color_eq_slotColor
    source layer v side).symm

theorem FKColoredStrandSplice.symm_bondCoherent
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source) :
    FKColoredStrandSpliceBondCoherent splice.target
      (fun layer => (source layer).pairing) splice.slotEquiv.symm := by
  intro x
  rw [splice.symm_rawColor, splice.symm_rawColor]
  rcases x with ⟨layer, d⟩
  exact (source layer).color_bondMate d


end
end StatMech.FrontierD
