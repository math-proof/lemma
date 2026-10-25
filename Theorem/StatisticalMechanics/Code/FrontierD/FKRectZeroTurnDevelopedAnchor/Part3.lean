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
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part2
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRawPrimalCrossingBase_component
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    (fkRectOpenGraph R
      (fkRectForceCutClosed R omega)).connectedComponentMk
        (fkRectRawPrimalCrossingBase R omega X) = X.1 := by
  exact fkRectRawPrimalCrossingFirstRow_component R omega X

theorem fkRectRawPrimalCrossingBase_torusComponent
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    (fkRectOpenGraph R omega).connectedComponentMk
        (fkRectRawPrimalCrossingBase R omega X) =
      fkRectRawPrimalCrossingTorusComponent R omega X := by
  unfold fkRectRawPrimalCrossingTorusComponent
  rw [← fkRectRawPrimalCrossingTorusComponent_mk R omega
    (fkRectRawPrimalCrossingBase R omega X),
    fkRectRawPrimalCrossingBase_component]


end
end StatMech.FrontierD
