/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectQuarterTurn.Part5
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem fkRectQuarterTurnEdgeInv_left
    (R : FKRectTorus) (hheight : 4 < R.height) (a : R.EdgeIndex) :
    fkRectQuarterTurnEdgeInv R hheight
        (fkRectQuarterTurnEdge R hheight a) = a := by
  rcases a with ⟨b, x, y⟩
  cases b <;> apply Prod.ext
  · simp [fkRectQuarterTurnEdgeInv, fkRectQuarterTurnEdge,
      fkRectParityBit]
  · apply Prod.ext <;> apply Fin.ext <;>
      simp [fkRectQuarterTurnEdgeInv, fkRectQuarterTurnEdge,
        fkRectParityBit_toNat] <;> omega
  · simp [fkRectQuarterTurnEdgeInv, fkRectQuarterTurnEdge,
      fkRectParityBit]
  · apply Prod.ext <;> apply Fin.ext <;>
      simp [fkRectQuarterTurnEdgeInv, fkRectQuarterTurnEdge,
        fkRectParityBit_toNat] <;> omega

theorem fkRectQuarterTurnEdgeInv_right
    (R : FKRectTorus) (hheight : 4 < R.height)
    (a : (fkRectQuarterTurnTorus R hheight).EdgeIndex) :
    fkRectQuarterTurnEdge R hheight
        (fkRectQuarterTurnEdgeInv R hheight a) = a := by
  rcases a with ⟨b, x, y⟩
  cases b <;> apply Prod.ext
  · simp [fkRectQuarterTurnEdgeInv, fkRectQuarterTurnEdge,
      fkRectParityBit]
  · apply Prod.ext <;> apply Fin.ext <;>
      simp [fkRectQuarterTurnEdgeInv, fkRectQuarterTurnEdge,
        fkRectParityBit_toNat] <;> omega
  · simp [fkRectQuarterTurnEdgeInv, fkRectQuarterTurnEdge,
      fkRectParityBit]
  · apply Prod.ext <;> apply Fin.ext <;>
      simp [fkRectQuarterTurnEdgeInv, fkRectQuarterTurnEdge,
        fkRectParityBit_toNat] <;> omega


end
end StatMech.FrontierD
