/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectQuarterTurn
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def fkRectQuarterTurnVertex (R : FKRectTorus) (hheight : 4 < R.height)
    (v : R.Vertex) : (fkRectQuarterTurnTorus R hheight).Vertex :=
  (⟨v.2.val / 2, by
      have hH := fkRectHeight_two_mul_div_two R
      simp only [fkRectQuarterTurnTorus]
      omega⟩,
   ⟨2 * v.1.val + v.2.val % 2, by
      simp only [fkRectQuarterTurnTorus]
      omega⟩)


def fkRectQuarterTurnVertexInv (R : FKRectTorus) (hheight : 4 < R.height)
    (v : (fkRectQuarterTurnTorus R hheight).Vertex) : R.Vertex :=
  (⟨v.2.val / 2, by
      simp only [fkRectQuarterTurnTorus] at v ⊢
      omega⟩,
   ⟨2 * v.1.val + v.2.val % 2, by
      have hH := fkRectHeight_two_mul_div_two R
      simp only [fkRectQuarterTurnTorus] at v ⊢
      omega⟩)

end
end StatMech.FrontierD
