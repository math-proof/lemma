/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingOneThermodynamicBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiagonalRate.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingBlockSource


namespace StatMech.FrontierD

noncomputable section

open Filter Topology


def fkRectWindingBlockPathVertex
    (k scale blocks cut : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) (i : Fin (blocks + 2)) :
    FKRectRightStripBandVertex
      (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
      ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1) := by
  let R := fkRectWindingBlockVerticalFamily k scale blocks
  let row := 1 + 2 * (scale + 1) * i.val
  have hi : i.val <= blocks + 1 := by omega
  have hmul : 2 * (scale + 1) * i.val <=
      2 * (scale + 1) * (blocks + 1) :=
    Nat.mul_le_mul_left (2 * (scale + 1)) hi
  have hrow : row < R.height := by
    dsimp [row, R, fkRectWindingBlockVerticalFamily]
    omega
  let y : Fin R.height := ⟨row, hrow⟩
  refine ⟨(x, y), ?_⟩
  change cut <= x.val ∧ 1 <= row ∧ row <= R.height - 1
  refine ⟨hx, by omega, ?_⟩
  dsimp [row, R, fkRectWindingBlockVerticalFamily]
  omega

end
end StatMech.FrontierD
