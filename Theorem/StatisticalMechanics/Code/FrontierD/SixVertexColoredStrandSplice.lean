/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkColoredSideSlot_west (pairing : Bool) :
    fkColoredSideSlot pairing .west = false := by
  cases pairing <;> rfl

@[simp] theorem fkColoredSideSlot_east (pairing : Bool) :
    fkColoredSideSlot pairing .east = true := by
  cases pairing <;> rfl

theorem fkColoredSideSlot_localMate
    (pairing : Bool) (side : FKMedialSide) :
    fkColoredSideSlot pairing (fkMedialLocalSideMate pairing side) =
      fkColoredSideSlot pairing side := by
  cases pairing <;> cases side <;> rfl

theorem FKColoredLoopPairing.color_eq_slotColor
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (layer : Bool) (v : T.Vertex) (side : FKMedialSide) :
    (source layer).color (v, side) =
      fkColoredLayeredSlotColor source
        (layer, v, fkColoredSideSlot ((source layer).pairing v) side) := by
  cases hp : (source layer).pairing v
  · cases side
    · simp [fkColoredLayeredSlotColor, fkColoredSideSlot]
    · simp [fkColoredLayeredSlotColor, fkColoredSideSlot]
    · simpa [fkColoredLayeredSlotColor, fkColoredSideSlot,
        fkMedialLocalMate, hp] using
        (source layer).color_localMate (v, .east)
    · simpa [fkColoredLayeredSlotColor, fkColoredSideSlot,
        fkMedialLocalMate, hp] using
        (source layer).color_localMate (v, .west)
  · cases side
    · simp [fkColoredLayeredSlotColor, fkColoredSideSlot]
    · simp [fkColoredLayeredSlotColor, fkColoredSideSlot]
    · simpa [fkColoredLayeredSlotColor, fkColoredSideSlot,
        fkMedialLocalMate, hp] using
        (source layer).color_localMate (v, .west)
    · simpa [fkColoredLayeredSlotColor, fkColoredSideSlot,
        fkMedialLocalMate, hp] using
        (source layer).color_localMate (v, .east)


end
end StatMech.FrontierD
