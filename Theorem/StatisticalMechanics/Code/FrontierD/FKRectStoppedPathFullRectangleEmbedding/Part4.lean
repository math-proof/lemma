/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectLocalBoxEmbedding.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectStoppedPathTwoChannelAdapter
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingBlockSource.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStoppedConditionalLaw.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectStoppedPathFullRectangleEmbedding.Part4
open SimpleGraph


namespace StatMech.FrontierD

open StatMech StatMech.Lattice

open StatMech.Universality

noncomputable section

theorem fkRectWindingStoppedRectangle_fits
    (k scale blocks : Nat)
    (hwidth : 12 * scale + 2 < 2 * (k + 3))
    (hblocks : 3 <= blocks) :
    FKRectLocalBoxFits
      (fkRectWindingBlockVerticalFamily k scale blocks)
      (fkRectWindingStoppedRectangleCenter
        k scale blocks hwidth hblocks)
      (2 * scale) 1 1
      ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1) := by
  apply fkRectLocalBoxFits_of_margin
  · exact Nat.sub_lt
      (fkRectWindingBlockVerticalFamily k scale blocks).height_pos
      (by omega)
  · change 1 + 2 * (2 * scale) <= 4 * scale + 1
    omega
  · change 4 * scale + 1 + 2 * (2 * scale) < 2 * (k + 3)
    omega
  · change 1 + 2 * (2 * scale) <= 4 * scale + 1
    omega
  · change 4 * scale + 1 + 2 * (2 * scale) <=
      (fkRectWindingBlockVerticalFamily k scale blocks).height - 1
    simp only [fkRectWindingBlockVerticalFamily_height]
    have hmul : (scale + 1) * 4 <= (scale + 1) * (blocks + 1) :=
      Nat.mul_le_mul_left (scale + 1) (by omega)
    rw [Nat.mul_assoc]
    omega


end
end StatMech.FrontierD
