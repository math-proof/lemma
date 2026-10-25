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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction.Part5
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectPrimalComponentPositiveBoundaryVerticalMass
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) : Nat := by
  classical
  exact ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
    if fkRectBlackBoundaryCyclePrimalComponent R omega C = K then
      (fkRectBlackBoundaryCycleWinding R omega C).2.toNat
    else 0


end
end StatMech.FrontierD
