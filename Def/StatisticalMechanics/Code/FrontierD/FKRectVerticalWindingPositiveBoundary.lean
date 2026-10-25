/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPositiveBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingBoundarySum
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingPositiveBoundary
open Equiv Finset


namespace StatMech.FrontierD

noncomputable section

def fkRectPositiveVerticalBoundaryWindingTotal
    (R : FKRectTorus) (omega : R.Configuration) : Nat :=
  ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
    (fkRectBlackBoundaryCycleWinding R omega C).2.toNat

end
end StatMech.FrontierD
