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
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part6
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRawPrimalCrossingBottomVertex_spec
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    fkRectRawPrimalCrossingBottomVertex R omega X ∈
        fkRectRawPrimalCrossingTorusVertices R omega X ∧
      fkRectRawPrimalCrossingDevelopedHeight R omega X
          (fkRectRawPrimalCrossingBottomVertex R omega X) =
        fkRectRawPrimalCrossingMinDevelopedHeight R omega X := by
  exact (fkRectRawPrimalCrossingBottomVertexWithSpec R omega X).2


end
end StatMech.FrontierD
