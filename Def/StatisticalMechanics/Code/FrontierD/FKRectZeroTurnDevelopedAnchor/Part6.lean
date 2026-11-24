module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleWinding.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenBoundaryDependence
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part6
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

noncomputable def fkRectRawPrimalCrossingMinDevelopedHeight
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) : Int :=
  (fkRectRawPrimalCrossingDevelopedHeights R omega X).min'
    (fkRectRawPrimalCrossingDevelopedHeights_nonempty R omega X)

noncomputable def fkRectRawPrimalCrossingMaxDevelopedHeight
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) : Int :=
  (fkRectRawPrimalCrossingDevelopedHeights R omega X).max'
    (fkRectRawPrimalCrossingDevelopedHeights_nonempty R omega X)


noncomputable def fkRectRawPrimalCrossingBottomVertexWithSpec
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    {y : R.Vertex //
      y ∈ fkRectRawPrimalCrossingTorusVertices R omega X ∧
      fkRectRawPrimalCrossingDevelopedHeight R omega X y =
        fkRectRawPrimalCrossingMinDevelopedHeight R omega X} := by
  have hmem : fkRectRawPrimalCrossingMinDevelopedHeight R omega X ∈
      fkRectRawPrimalCrossingDevelopedHeights R omega X :=
    Finset.min'_mem _ _
  let hex := Finset.mem_image.mp hmem
  exact ⟨Classical.choose hex, (Classical.choose_spec hex).1,
    (Classical.choose_spec hex).2⟩


noncomputable def fkRectRawPrimalCrossingBottomVertex
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) : R.Vertex :=
  fkRectRawPrimalCrossingBottomVertexWithSpec R omega X

end
end StatMech.FrontierD
