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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part7
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectRawPrimalCrossingTopVertexWithSpec
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    {y : R.Vertex //
      y ∈ fkRectRawPrimalCrossingTorusVertices R omega X ∧
      fkRectRawPrimalCrossingDevelopedHeight R omega X y =
        fkRectRawPrimalCrossingMaxDevelopedHeight R omega X} := by
  have hmem : fkRectRawPrimalCrossingMaxDevelopedHeight R omega X ∈
      fkRectRawPrimalCrossingDevelopedHeights R omega X :=
    Finset.max'_mem _ _
  let hex := Finset.mem_image.mp hmem
  exact ⟨Classical.choose hex, (Classical.choose_spec hex).1,
    (Classical.choose_spec hex).2⟩


noncomputable def fkRectRawPrimalCrossingTopVertex
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) : R.Vertex :=
  fkRectRawPrimalCrossingTopVertexWithSpec R omega X

end
end StatMech.FrontierD
