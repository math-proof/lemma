module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingPositiveBoundary.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part6
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEssentialClusterBoundary.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction.Part7
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberReduction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def FKRectPrimalComponentHasNet
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) : Prop :=
  ∃ p q : (fkRectOpenGraph R omega).Walk K.out K.out,
    FKRectWindingIndependent
      (fkRectWalkWinding R p) (fkRectWalkWinding R q)


end
end StatMech.FrontierD
