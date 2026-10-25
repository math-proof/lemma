/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part6


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourAuditedParamVerticalRowsFirst
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam : Fin 4) :
    Fin 4 -> SixVertexRow 4 :=
  let horizontal := sixVertexFourByFourAuditedParamHorizontalRowsFirst p
  let seamRow :=
    sixVertexFourByFourRowOfMask (sixVertexFourByFourSectorOneSeamMask seam)
  let verticalZero :=
    sixVertexFourByFourNextVerticalRow (horizontal 0) seamRow
  let verticalOne :=
    sixVertexFourByFourNextVerticalRow (horizontal 1) verticalZero
  let verticalTwo :=
    sixVertexFourByFourNextVerticalRow (horizontal 2) verticalOne
  let verticalThree :=
    sixVertexFourByFourNextVerticalRow (horizontal 3) verticalTwo
  ![verticalZero, verticalOne, verticalTwo, verticalThree]

def sixVertexFourByFourAuditedParamVerticalRowsSecond
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam : Fin 4) :
    Fin 4 -> SixVertexRow 4 :=
  let horizontal := sixVertexFourByFourAuditedParamHorizontalRowsSecond p
  let seamRow :=
    sixVertexFourByFourRowOfMask (sixVertexFourByFourSectorThreeSeamMask seam)
  let verticalZero :=
    sixVertexFourByFourNextVerticalRow (horizontal 0) seamRow
  let verticalOne :=
    sixVertexFourByFourNextVerticalRow (horizontal 1) verticalZero
  let verticalTwo :=
    sixVertexFourByFourNextVerticalRow (horizontal 2) verticalOne
  let verticalThree :=
    sixVertexFourByFourNextVerticalRow (horizontal 3) verticalTwo
  ![verticalZero, verticalOne, verticalTwo, verticalThree]

def sixVertexFourByFourVerticalMaskOfRows
    (rows : Fin 4 -> SixVertexRow 4) : Nat :=
  Nat.ofBits fun i : Fin 16 =>
    let yx := (finProdFinEquiv (m := 4) (n := 4)).symm i
    rows yx.1 yx.2

end
end StatMech.FrontierD
