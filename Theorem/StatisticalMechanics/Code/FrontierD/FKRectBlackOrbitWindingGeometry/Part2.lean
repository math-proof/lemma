/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part8
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part2


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

@[simp] theorem fkRectMedialRibbonBlock_length
    (pairing : Bool) (side : FKMedialSide) :
    (fkRectMedialRibbonBlock pairing side).length = 8 := by
  cases pairing <;> cases side <;>
    simp [fkRectMedialRibbonBlock, fkRectMedialRibbonLocalBlock]


theorem fkRectMedialRibbonBlock_step_sum
    (pairing : Bool) (side : FKMedialSide) :
    let medialDir := fkRectMedialSideDirection
      (fkRectMedialLocalMateSide pairing side)
    let nextSide := fkRectMedialOppositeSide
      (fkRectMedialLocalMateSide pairing side)
    ((fkRectMedialRibbonBlock pairing side).map stepOf).sum =
      (8 * (stepOf medialDir).1 +
          (fkRectMedialRibbonPortOffset nextSide).1 -
          (fkRectMedialRibbonPortOffset side).1,
        8 * (stepOf medialDir).2 +
          (fkRectMedialRibbonPortOffset nextSide).2 -
          (fkRectMedialRibbonPortOffset side).2) := by
  cases pairing <;> cases side <;>
    decide

theorem fkRectMedialOppositeSide_localMate_eq_boundaryPerm_side
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialBlackDart T) :
    fkRectMedialOppositeSide (fkMedialLocalMate pairing d.1).2 =
      (fkMedialBlackBoundaryPerm pairing d).1.2 := by
  rcases d with ⟨⟨v, side⟩, hd⟩
  cases hp : pairing v <;> cases side <;>
    simp [fkRectMedialOppositeSide, fkMedialBlackBoundaryPerm_val,
      fkMedialLocalMate, fkMedialBondMate, hp]


end
end StatMech.FrontierD
