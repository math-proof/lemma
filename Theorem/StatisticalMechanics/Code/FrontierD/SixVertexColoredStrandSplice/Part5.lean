/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkColoredStrandSlotEquivOfFiberCards_color
    {T : EvenTorus} (source target : FKColoredLoopPairingPair T)
    (hcard : forall color : Bool,
      Fintype.card {slot : FKLayeredStrandSlot T //
          fkColoredLayeredSlotColor target slot = color} =
        Fintype.card {slot : FKLayeredStrandSlot T //
          fkColoredLayeredSlotColor source slot = color}) :
    FKColoredStrandSlotColorEquiv source target
      (fkColoredStrandSlotEquivOfFiberCards source target hcard) := by
  intro slot
  rw [fkColoredStrandSlotEquivOfFiberCards,
    Equiv.ofFiberEquiv_apply]
  exact (Fintype.equivOfCardEq
    (hcard (fkColoredLayeredSlotColor target slot))
    ((Equiv.sigmaFiberEquiv
      (fkColoredLayeredSlotColor target)).symm slot).snd).2

theorem fkColoredStrandSlotFiberCards_of_trueCount_eq
    {T : EvenTorus} (source target : FKColoredLoopPairingPair T)
    (htrue : fkColoredTrueStrandSlotCount source =
      fkColoredTrueStrandSlotCount target) :
    forall color : Bool,
      Fintype.card {slot : FKLayeredStrandSlot T //
          fkColoredLayeredSlotColor target slot = color} =
        Fintype.card {slot : FKLayeredStrandSlot T //
          fkColoredLayeredSlotColor source slot = color} := by
  intro color
  cases color
  · rw [card_boolFalseFiber, card_boolFalseFiber]
    unfold fkColoredTrueStrandSlotCount at htrue
    rw [← htrue]
  · exact htrue.symm

end
end StatMech.FrontierD
