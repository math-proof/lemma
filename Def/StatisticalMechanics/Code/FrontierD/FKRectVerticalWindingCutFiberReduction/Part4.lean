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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction.Part4
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def FKRectVerticalBoundaryMassCutFiberBound
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  ∀ K : (fkRectOpenGraph R omega).ConnectedComponent,
    fkRectPrimalComponentBoundaryVerticalMass R omega K ≤
      2 * fkRectPrimalComponentHorizontalCutCrossingCount R omega K


end
end StatMech.FrontierD
