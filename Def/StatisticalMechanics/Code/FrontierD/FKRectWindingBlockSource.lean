/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingOneThermodynamicBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiagonalRate.Part3


namespace StatMech.FrontierD

noncomputable section

open Filter Topology


def fkRectWindingBlockVerticalFamily
    (k scale blocks : Nat) : FKRectTorus where
  width := 2 * (k + 3)
  height := 2 * (scale + 1) * (blocks + 1) + 2
  width_gt_two := by omega
  height_gt_two := by
    have h : 0 < 2 * (scale + 1) * (blocks + 1) :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    omega
  height_even := ⟨(scale + 1) * (blocks + 1) + 1, by ring⟩

end
end StatMech.FrontierD
