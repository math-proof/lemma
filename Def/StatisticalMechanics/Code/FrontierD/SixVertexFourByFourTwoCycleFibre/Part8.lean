/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part7


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourVerticalNext
    (horizontalMask : Nat) (x y : Fin 4) (below : Bool) : Bool :=
  decide
    ((horizontalMask.testBit
          (y.val * 4 + (SixVertexArrows.cyclicPred (by norm_num) x).val)).toNat +
        (!horizontalMask.testBit (y.val * 4 + x.val)).toNat +
        below.toNat = 2)

def sixVertexFourByFourCompletedVerticalColumn
    (horizontalMask seamMask : Nat) (x : Fin 4) : Fin 4 -> Bool :=
  let seam := seamMask.testBit x.val
  let v0 := sixVertexFourByFourVerticalNext horizontalMask x 0 seam
  let v1 := sixVertexFourByFourVerticalNext horizontalMask x 1 v0
  let v2 := sixVertexFourByFourVerticalNext horizontalMask x 2 v1
  let v3 := sixVertexFourByFourVerticalNext horizontalMask x 3 v2
  ![v0, v1, v2, v3]

def sixVertexFourByFourCompletedVerticalMask
    (horizontalMask seamMask : Nat) : Nat :=
  Nat.ofBits fun i : Fin 16 =>
    let yx := (finProdFinEquiv (m := 4) (n := 4)).symm i
    sixVertexFourByFourCompletedVerticalColumn
      horizontalMask seamMask yx.2 yx.1

def sixVertexFourByFourCompletedVerticalRow
    (horizontalMask seamMask : Nat) (y : Fin 4) : SixVertexRow 4 :=
  fun x => sixVertexFourByFourCompletedVerticalColumn horizontalMask seamMask x y

end
end StatMech.FrontierD
