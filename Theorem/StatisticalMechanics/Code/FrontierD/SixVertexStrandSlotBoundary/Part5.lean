/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part5


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkColoredLayeredStrandSlotBoundaryPerm_apply
    {T : EvenTorus} (pairing : Bool -> FKMedialLoopPairing T)
    (slot : FKLayeredStrandSlot T) :
    fkColoredLayeredStrandSlotBoundaryPerm pairing slot =
      (slot.1,
        fkColoredStrandSlotBoundaryPerm (pairing slot.1) slot.2) := rfl

theorem fkColoredLayeredSlotColor_boundaryPerm
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (slot : FKLayeredStrandSlot T) :
    fkColoredLayeredSlotColor source
        (fkColoredLayeredStrandSlotBoundaryPerm
          (fun layer => (source layer).pairing) slot) =
      fkColoredLayeredSlotColor source slot := by
  rcases slot with ⟨layer, slot⟩
  exact FKColoredLoopPairing.slotColor_boundaryPerm source layer slot


end
end StatMech.FrontierD
