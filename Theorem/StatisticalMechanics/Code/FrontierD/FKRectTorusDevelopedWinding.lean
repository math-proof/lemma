/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDevelopedWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingSubgroup.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectDevelopedStep_swap (R : FKRectTorus) (x y : R.Vertex) :
    fkRectDevelopedStep R y x = -fkRectDevelopedStep R x y := by
  unfold fkRectDevelopedStep
  rw [fkRectHorizontalSeamIncrement_swap,
    fkRectVerticalSeamIncrement_swap]
  apply Prod.ext <;> simp <;> ring


end
end StatMech.FrontierD
