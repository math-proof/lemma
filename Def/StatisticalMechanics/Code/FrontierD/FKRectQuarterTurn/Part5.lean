/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectQuarterTurn.Part4
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def fkRectQuarterTurnEdge (R : FKRectTorus) (hheight : 4 < R.height)
    (a : R.EdgeIndex) : (fkRectQuarterTurnTorus R hheight).EdgeIndex :=
  (fkRectParityBit a.2.2.val,
    (⟨a.2.2.val / 2, by
        have hH := fkRectHeight_two_mul_div_two R
        simp only [fkRectQuarterTurnTorus]
        omega⟩,
     ⟨2 * a.2.1.val + a.1.toNat, by
        simp only [fkRectQuarterTurnTorus]
        cases a.1 <;> simp <;> omega⟩))


def fkRectQuarterTurnEdgeInv (R : FKRectTorus) (hheight : 4 < R.height)
    (a : (fkRectQuarterTurnTorus R hheight).EdgeIndex) : R.EdgeIndex :=
  (fkRectParityBit a.2.2.val,
    (⟨a.2.2.val / 2, by
        simp only [fkRectQuarterTurnTorus] at a ⊢
        omega⟩,
     ⟨2 * a.2.1.val + a.1.toNat, by
        have hH := fkRectHeight_two_mul_div_two R
        simp only [fkRectQuarterTurnTorus] at a ⊢
        cases a.1 <;> simp <;> omega⟩))

end
end StatMech.FrontierD
