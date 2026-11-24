module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleWinding.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenBoundaryDependence
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part2
open Equiv Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectRawPrimalCrossingBase
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) : R.Vertex :=
  (fkRectLeftColumn R, fkRectRawPrimalCrossingFirstRow R omega X)

end
end StatMech.FrontierD
