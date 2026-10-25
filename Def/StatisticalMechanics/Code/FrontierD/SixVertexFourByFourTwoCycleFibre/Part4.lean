/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part3


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourAuditedHorizontalMasks
    (p : SixVertexFourByFourAuditedHorizontalParameters) : Nat × Nat :=
  let rowZero := sixVertexFourByFourAuditedRowZero p.1
  let rowOne := sixVertexFourByFourAuditedRowMiddle p.2.1
  let rowTwo := sixVertexFourByFourAuditedRowMiddle p.2.2.1
  let rowThree := sixVertexFourByFourAuditedRowLast p.2.2.2
  (sixVertexFourByFourMaskOfRowMasks
      ![rowZero.1, rowOne.1, rowTwo.1, rowThree.1],
    sixVertexFourByFourMaskOfRowMasks
      ![rowZero.2, rowOne.2, rowTwo.2, rowThree.2])

def sixVertexFourByFourSectorOneSeamMask : Fin 4 -> Nat := ![1, 2, 4, 8]

def sixVertexFourByFourSectorThreeSeamMask : Fin 4 -> Nat := ![7, 11, 13, 14]

def sixVertexFourByFourRowOfMask (mask : Nat) : SixVertexRow 4 :=
  fun x => mask.testBit x.val

def sixVertexFourByFourNextVerticalRow
    (horizontal below : SixVertexRow 4) : SixVertexRow 4 :=
  fun x => decide
    ((horizontal (SixVertexArrows.cyclicPred (by norm_num) x)).toNat +
        (!horizontal x).toNat + (below x).toNat = 2)

def sixVertexFourByFourEvenUpCount (row : SixVertexRow 4) : Nat :=
  (row 0).toNat + (row 2).toNat

def sixVertexFourByFourAllowedHorizontalMask : Fin 6 -> Nat :=
  ![0, 3, 6, 9, 12, 15]

end
end StatMech.FrontierD
