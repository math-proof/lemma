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
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectOpenGraph_forceHorizontalCutClosed_le
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega) ≤
      fkRectOpenGraph R omega := by
  apply fkRectOpenGraph_mono R
  intro e he
  by_cases hcut : e ∈ fkRectHorizontalCutEdges R
  · simp [fkRectForceHorizontalCutClosed, hcut] at he
  · simpa [fkRectForceHorizontalCutClosed, hcut] using he


end
end StatMech.FrontierD
