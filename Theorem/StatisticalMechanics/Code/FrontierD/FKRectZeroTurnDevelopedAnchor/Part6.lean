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
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part5
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRawPrimalCrossingDevelopedHeights_nonempty
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    (fkRectRawPrimalCrossingDevelopedHeights R omega X).Nonempty := by
  obtain ⟨y, hy⟩ := fkRectRawPrimalCrossingTorusVertices_nonempty R omega X
  exact ⟨fkRectRawPrimalCrossingDevelopedHeight R omega X y,
    Finset.mem_image.mpr ⟨y, hy, rfl⟩⟩

end
end StatMech.FrontierD
