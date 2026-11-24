module
public import Theorem.StatisticalMechanics.Code.FrontierD.PermOrbitWeightSum
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryCycleWeight
open Equiv Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleWeight.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectBoundaryCycleClassWinding
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) : Int × Int :=
  permCycleClassWeightSum (fkMedialBoundaryStep pairing) d
    (fkRectMedialBoundaryPrimalSeamIncrement R pairing)


end
end StatMech.FrontierD
