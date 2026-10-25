/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialBoundaryWalk.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundary


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkMedialLocalMate_side
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) :
    (fkMedialLocalMate pairing d).2 =
      fkRectMedialLocalMateSide (pairing d.1) d.2 := by
  rcases d with ⟨v, side⟩
  cases h : pairing v <;> cases side <;>
    simp [fkMedialLocalMate, fkRectMedialLocalMateSide, h]

theorem fkRectRefinedDartPoint_bondMate
    (T : EvenTorus) (c : Int × Int) (d : FKMedialDart T) :
    fkRectRefinedDartPoint
        (fkRectRefinedBondCenter c d.2)
        (fkMedialBondMate T d).2 =
      fkRectRefinedDartPoint c d.2 := by
  rcases d with ⟨v, side⟩
  cases side <;>
    simp [fkRectRefinedDartPoint, fkRectRefinedBondCenter,
      fkRectRefinedSideOffset, fkMedialBondMate] <;> ring_nf <;> simp


end
end StatMech.FrontierD
