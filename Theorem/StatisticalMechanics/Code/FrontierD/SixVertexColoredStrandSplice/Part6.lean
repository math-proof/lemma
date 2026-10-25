/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkColoredStrandSlotEquivOfTrueCount_color
    {T : EvenTorus} (source target : FKColoredLoopPairingPair T)
    (htrue : fkColoredTrueStrandSlotCount source =
      fkColoredTrueStrandSlotCount target) :
    FKColoredStrandSlotColorEquiv source target
      (fkColoredStrandSlotEquivOfTrueCount source target htrue) :=
  fkColoredStrandSlotEquivOfFiberCards_color source target _

theorem fkColoredStrandSpliceRawColor_eq_of_colorEquiv
    {T : EvenTorus} (source target : FKColoredLoopPairingPair T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T)
    (hcolor : FKColoredStrandSlotColorEquiv source target slotEquiv)
    (x : FKLayeredMedialDart T) :
    fkColoredStrandSpliceRawColor source
        (fun layer => (target layer).pairing) slotEquiv x =
      (target x.1).color x.2 := by
  rcases x with ⟨layer, v, side⟩
  unfold fkColoredStrandSpliceRawColor
  rw [hcolor]
  exact (FKColoredLoopPairing.color_eq_slotColor
    target layer v side).symm


end
end StatMech.FrontierD
