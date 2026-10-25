/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part2


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkColoredLoopPairingPairSwapLayers_slotColor
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (slot : FKLayeredStrandSlot T) :
    fkColoredLayeredSlotColor (fkColoredLoopPairingPairSwapLayers source) slot =
      fkColoredLayeredSlotColor source
        (fkColoredLayeredStrandSlotSwapLayers slot) := by
  rcases slot with ⟨layer, vertex, side⟩
  cases layer <;> rfl


theorem fkColoredLoopPairingPairSwapLayers_trueStrandSlotCount
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) :
    fkColoredTrueStrandSlotCount
        (fkColoredLoopPairingPairSwapLayers source) =
      fkColoredTrueStrandSlotCount source := by
  unfold fkColoredTrueStrandSlotCount
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv fkColoredLayeredStrandSlotSwapLayers
  intro slot
  rw [fkColoredLoopPairingPairSwapLayers_slotColor]


@[simp] theorem fkColoredLoopPairingPairSwapLayers_totalC
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) :
    fkColoredLoopPairingPairTotalC
        (fkColoredLoopPairingPairSwapLayers source) =
      fkColoredLoopPairingPairTotalC source := by
  simp [fkColoredLoopPairingPairTotalC,
    fkColoredLoopPairingPairSwapLayers, add_comm]


theorem sixVertexPairAtMostTwoCycleRelated_swap_target
    {T : EvenTorus}
    {source target : SixVertexArrows T × SixVertexArrows T}
    (hrelated : sixVertexPairAtMostTwoCycleRelated source target) :
    sixVertexPairAtMostTwoCycleRelated source (target.2, target.1) := by
  rcases target with ⟨targetFirst, targetSecond⟩
  rcases hrelated with ⟨family, sign, hhorizontal, hvertical⟩
  refine ⟨family, sign, ?_, ?_⟩
  · rw [← hhorizontal]
    funext v
    unfold sixVertexPairUnionHorizontalDelta sixVertexPairUnionHorizontal
    simp only
    omega
  · rw [← hvertical]
    funext v
    unfold sixVertexPairUnionVerticalDelta sixVertexPairUnionVertical
    simp only
    omega


end
end StatMech.FrontierD
