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
import Def.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction.Part5
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem sum_fkRectPrimalComponentPositiveBoundaryVerticalMass
    (R : FKRectTorus) (omega : R.Configuration) :
    ∑ K : (fkRectOpenGraph R omega).ConnectedComponent,
        fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K =
      fkRectPositiveVerticalBoundaryWindingTotal R omega := by
  classical
  unfold fkRectPrimalComponentPositiveBoundaryVerticalMass
    fkRectPositiveVerticalBoundaryWindingTotal
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  rw [Finset.sum_eq_single
    (fkRectBlackBoundaryCyclePrimalComponent R omega C)]
  · simp
  · intro K _ hne
    simp [Ne.symm hne]
  · simp


end
end StatMech.FrontierD
