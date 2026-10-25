/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialBoundaryWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialReachability
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part7
import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialBoundaryWalk
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectMedialBoundaryPrimalStepWalk_length_le_one
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    (fkRectMedialBoundaryPrimalStepWalk R omega d).length ≤ 1 := by
  unfold fkRectMedialBoundaryPrimalStepWalk
  split <;> simp


end
end StatMech.FrontierD
