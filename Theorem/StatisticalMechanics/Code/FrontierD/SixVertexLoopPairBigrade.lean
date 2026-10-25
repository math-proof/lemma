/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopPairBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part11
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLoopPairBigrade


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexLoopDecoratedPairColored_false_arrows
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right) :
    (sixVertexLoopDecoratedPairColored decorated false).arrows =
      decorated.1.1.1 :=
  SixVertexCompatibleLoopPairing.toColored_arrows _

@[simp] theorem sixVertexLoopDecoratedPairColored_true_arrows
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right) :
    (sixVertexLoopDecoratedPairColored decorated true).arrows =
      decorated.1.2.1 :=
  SixVertexCompatibleLoopPairing.toColored_arrows _

theorem sixVertexLoopDecoratedPairColored_totalC
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right) :
    fkColoredLoopPairingPairTotalC
        (sixVertexLoopDecoratedPairColored decorated) =
      sixVertexLoopDecoratedPairTotalC decorated := by
  simp [fkColoredLoopPairingPairTotalC,
    sixVertexLoopDecoratedPairTotalC,
    sixVertexConfigurationPairTotalC]

theorem sixVertexLoopDecoratedPairColored_slotColor
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right)
    (slot : FKLayeredStrandSlot T) :
    fkColoredLayeredSlotColor
        (sixVertexLoopDecoratedPairColored decorated) slot =
      sixVertexArrowPairStrandSlotColor
        decorated.1.1.1 decorated.1.2.1 slot := by
  rcases slot with ⟨layer, v, side⟩
  cases layer <;> cases side <;> rfl

theorem sixVertexLoopDecoratedPairColored_trueSlotCount
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right) :
    fkColoredTrueStrandSlotCount
        (sixVertexLoopDecoratedPairColored decorated) =
      sixVertexArrowPairTrueStrandSlotCount
        decorated.1.1.1 decorated.1.2.1 := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv (Equiv.refl _)
  intro slot
  change (fkColoredLayeredSlotColor
      (sixVertexLoopDecoratedPairColored decorated) slot = true) ↔ _
  simp [sixVertexLoopDecoratedPairColored_slotColor]


end
end StatMech.FrontierD
