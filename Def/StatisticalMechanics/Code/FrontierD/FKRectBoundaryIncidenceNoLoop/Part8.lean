module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceConnected.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveMixedNoLoopHeight
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part9
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceNoLoop.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

open Filter Topology


def FKRectPrimalRankOneRegularNeighborhood.ofBoundaryIncidence
    (R : FKRectTorus) (omega : R.Configuration)
    (hextreme : FKRectPrimalDevelopedExtremeSameSign R omega) :
    FKRectPrimalRankOneRegularNeighborhood R omega :=
  FKRectPrimalRankOneRegularNeighborhood.ofParts R omega
    (fkRectPrimalBoundaryFiberSameSignUnique_unconditional R omega) hextreme


end
end StatMech.FrontierD
