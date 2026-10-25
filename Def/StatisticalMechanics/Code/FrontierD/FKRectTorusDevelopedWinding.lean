/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDevelopedWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingSubgroup.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectDevelopedStep (R : FKRectTorus) (x y : R.Vertex) : Int × Int :=
  ((y.1.val : Int) - x.1.val +
      (R.width : Int) * fkRectHorizontalSeamIncrement R x y,
    (y.2.val : Int) - x.2.val +
      (R.height : Int) * fkRectVerticalSeamIncrement R x y)

end
end StatMech.FrontierD
