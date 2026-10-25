/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingOneThermodynamicBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiagonalRate.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectWindingBlockSource


namespace StatMech.FrontierD

noncomputable section

open Filter Topology


@[simp] theorem fkRectWindingBlockVerticalFamily_width
    (k scale blocks : Nat) :
    (fkRectWindingBlockVerticalFamily k scale blocks).width =
      2 * (k + 3) := rfl

@[simp] theorem fkRectWindingBlockVerticalFamily_height
    (k scale blocks : Nat) :
    (fkRectWindingBlockVerticalFamily k scale blocks).height =
      2 * (scale + 1) * (blocks + 1) + 2 := rfl

@[simp] theorem fkRectWindingBlockVerticalFamily_medialWidth
    (k scale blocks : Nat) :
    (fkRectWindingBlockVerticalFamily k scale blocks).medialTorus.width =
      sixVertexFourWidth 1 (k + 1) := by
  change 2 * (2 * (k + 3)) = 4 * (1 + (k + 1) + 1)
  omega

@[simp] theorem fkRectWindingBlockVerticalFamily_medialHeight
    (k scale blocks : Nat) :
    (fkRectWindingBlockVerticalFamily k scale blocks).medialTorus.height =
      2 * (scale + 1) * (blocks + 1) + 2 := rfl


end
end StatMech.FrontierD
