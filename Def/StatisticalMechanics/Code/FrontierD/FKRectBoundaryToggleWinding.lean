module
public import Theorem.StatisticalMechanics.Code.FrontierD.PermSameCycleWeightSplit
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryCycleWeight.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialToggle.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialClosedCycles.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleExact
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenBoundaryDependence
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingInsertion.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleWinding
open Equiv Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryToggleWinding.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
