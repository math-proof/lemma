/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleWeight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.PermOrbitWeightSum
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryCycleWeight
open Equiv Finset


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
