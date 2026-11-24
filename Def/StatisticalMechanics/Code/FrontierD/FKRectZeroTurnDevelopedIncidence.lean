module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedExtremeClosed
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryPotentialContradiction
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryFiberWinding.Part5
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectRawPrimalCrossingDevelopedExtremeEdge
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool) : R.EdgeIndex :=
  fkRectTorusMedialEdgeEquiv R
    (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side).1

end
end StatMech.FrontierD
