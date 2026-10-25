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
import Def.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction.Part4
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectUnorientedVerticalWindingTotal_le_two_mul_horizontalCut_of_fiberBound
    (R : FKRectTorus) (omega : R.Configuration)
    (h : FKRectVerticalBoundaryMassCutFiberBound R omega) :
    fkRectUnorientedVerticalWindingTotal R omega ≤
      2 * fkRectHorizontalCutPrimalCrossingClusterCount R
        (fkRectForceHorizontalCutClosed R omega) := by
  rw [fkRectUnorientedVerticalWindingTotal,
    fkRectUnorientedVerticalWindingTotal_eq_sum_blackBoundaryCycle,
    ← sum_fkRectPrimalComponentBoundaryVerticalMass R omega]
  calc
    _ ≤ ∑ K : (fkRectOpenGraph R omega).ConnectedComponent,
        2 * fkRectPrimalComponentHorizontalCutCrossingCount R omega K := by
      exact Finset.sum_le_sum fun K _ => h K
    _ = 2 * ∑ K : (fkRectOpenGraph R omega).ConnectedComponent,
        fkRectPrimalComponentHorizontalCutCrossingCount R omega K := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [sum_fkRectPrimalComponentHorizontalCutCrossingCount]


theorem fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_fiberBound
    (R : FKRectTorus) (omega : R.Configuration)
    (h : FKRectVerticalBoundaryMassCutFiberBound R omega) :
    fkRectUnorientedVerticalWindingNumber R omega ≤
      fkRectHorizontalCutPrimalCrossingClusterCount R
        (fkRectForceHorizontalCutClosed R omega) := by
  have htotal :=
    fkRectUnorientedVerticalWindingTotal_le_two_mul_horizontalCut_of_fiberBound
      R omega h
  unfold fkRectUnorientedVerticalWindingNumber
  omega


end
end StatMech.FrontierD
