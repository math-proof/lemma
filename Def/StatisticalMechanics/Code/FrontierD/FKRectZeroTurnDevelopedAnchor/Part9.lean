/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenBoundaryDependence
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part9
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectRawPrimalCrossingDevelopedExtremeDart
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool) : FKMedialDart R.medialTorus :=
  if side then
    fkRectMedialDartAbovePrimalVertex R
      (fkRectRawPrimalCrossingTopVertex R omega X)
  else
    fkRectMedialDartAtPrimalVertex R
      (fkRectRawPrimalCrossingBottomVertex R omega X)

end
end StatMech.FrontierD
