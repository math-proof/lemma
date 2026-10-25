/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingPositiveBoundary.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEssentialClusterBoundary.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction.Part6
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_positiveFiberBound
    (R : FKRectTorus) (omega : R.Configuration)
    (h : FKRectPositiveVerticalBoundaryCutFiberBound R omega) :
    fkRectUnorientedVerticalWindingNumber R omega ≤
      fkRectHorizontalCutPrimalCrossingClusterCount R
        (fkRectForceHorizontalCutClosed R omega) := by
  rw [fkRectUnorientedVerticalWindingNumber_eq_positiveBoundary,
    ← sum_fkRectPrimalComponentPositiveBoundaryVerticalMass R omega,
    ← sum_fkRectPrimalComponentHorizontalCutCrossingCount R omega]
  exact Finset.sum_le_sum fun K _ => h K


end
end StatMech.FrontierD
