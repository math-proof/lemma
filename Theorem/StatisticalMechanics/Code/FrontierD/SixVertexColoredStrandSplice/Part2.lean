/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkColoredStrandSpliceRawColor_localMate
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T)
    (layer : Bool) (d : FKMedialDart T) :
    fkColoredStrandSpliceRawColor source targetPairing slotEquiv
        (layer, fkMedialLocalMate (targetPairing layer) d) =
      fkColoredStrandSpliceRawColor source targetPairing slotEquiv
        (layer, d) := by
  rcases d with ⟨v, side⟩
  rw [fkMedialLocalMate_eq_localSideMate]
  unfold fkColoredStrandSpliceRawColor
  rw [fkColoredSideSlot_localMate]

end
end StatMech.FrontierD
