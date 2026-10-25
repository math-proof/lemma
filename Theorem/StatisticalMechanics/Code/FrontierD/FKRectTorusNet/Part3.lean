/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEulerDefect.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusNet.Part3
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectNetIndicator_eq_one_iff
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectNetIndicator R omega = 1 ↔ FKRectHasNet R omega := by
  classical
  unfold fkRectNetIndicator
  by_cases h : FKRectHasNet R omega <;> simp [h]

theorem fkRectNetIndicator_eq_zero_iff
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectNetIndicator R omega = 0 ↔ ¬ FKRectHasNet R omega := by
  classical
  unfold fkRectNetIndicator
  by_cases h : FKRectHasNet R omega <;> simp [h]

theorem fkRectNetIndicator_le_one
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectNetIndicator R omega ≤ 1 := by
  classical
  unfold fkRectNetIndicator
  split <;> omega

end
end StatMech.FrontierD
