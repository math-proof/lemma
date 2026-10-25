/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectQuarterTurn.Part2
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectQuarterTurnVertex_fst_val
    (R : FKRectTorus) (hheight : 4 < R.height) (v : R.Vertex) :
    (fkRectQuarterTurnVertex R hheight v).1.val = v.2.val / 2 := rfl

@[simp] theorem fkRectQuarterTurnVertex_snd_val
    (R : FKRectTorus) (hheight : 4 < R.height) (v : R.Vertex) :
    (fkRectQuarterTurnVertex R hheight v).2.val =
      2 * v.1.val + v.2.val % 2 := rfl

theorem fkRectQuarterTurnVertexInv_left
    (R : FKRectTorus) (hheight : 4 < R.height) (v : R.Vertex) :
    fkRectQuarterTurnVertexInv R hheight
        (fkRectQuarterTurnVertex R hheight v) = v := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [fkRectQuarterTurnVertexInv, fkRectQuarterTurnVertex] <;> omega

theorem fkRectQuarterTurnVertexInv_right
    (R : FKRectTorus) (hheight : 4 < R.height)
    (v : (fkRectQuarterTurnTorus R hheight).Vertex) :
    fkRectQuarterTurnVertex R hheight
        (fkRectQuarterTurnVertexInv R hheight v) = v := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [fkRectQuarterTurnVertexInv, fkRectQuarterTurnVertex] <;> omega


end
end StatMech.FrontierD
