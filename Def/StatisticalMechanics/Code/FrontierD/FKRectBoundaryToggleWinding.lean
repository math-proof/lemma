/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryToggleWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.PermSameCycleWeightSplit
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryCycleWeight.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialToggle.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialClosedCycles.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleExact
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenBoundaryDependence
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingInsertion.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleWinding
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectBlackBoundaryWeight (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) : Int × Int :=
  fkRectMedialBoundaryPrimalSeamIncrement R pairing d.1

def fkRectBlackBoundaryCycleClassWinding
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) : Int × Int :=
  permCycleClassWeightSum (fkMedialBlackBoundaryPerm pairing) d
    (fkRectBlackBoundaryWeight R pairing)

end
end StatMech.FrontierD
