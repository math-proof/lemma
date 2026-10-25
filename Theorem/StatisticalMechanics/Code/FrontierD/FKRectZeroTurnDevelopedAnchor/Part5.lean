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
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part4
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem mem_fkRectRawPrimalCrossingTorusVertices
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (y : R.Vertex) :
    y ∈ fkRectRawPrimalCrossingTorusVertices R omega X ↔
      (fkRectOpenGraph R omega).connectedComponentMk y =
        fkRectRawPrimalCrossingTorusComponent R omega X := by
  classical
  simp [fkRectRawPrimalCrossingTorusVertices]

theorem fkRectRawPrimalCrossingBase_mem_torusVertices
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    fkRectRawPrimalCrossingBase R omega X ∈
      fkRectRawPrimalCrossingTorusVertices R omega X := by
  rw [mem_fkRectRawPrimalCrossingTorusVertices,
    fkRectRawPrimalCrossingBase_torusComponent]

theorem fkRectRawPrimalCrossingTorusVertices_nonempty
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    (fkRectRawPrimalCrossingTorusVertices R omega X).Nonempty :=
  ⟨fkRectRawPrimalCrossingBase R omega X,
    fkRectRawPrimalCrossingBase_mem_torusVertices R omega X⟩

theorem fkRectRawPrimalCrossingBase_reachable_of_mem_torusVertices
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    {y : R.Vertex}
    (hy : y ∈ fkRectRawPrimalCrossingTorusVertices R omega X) :
    (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) y := by
  apply SimpleGraph.ConnectedComponent.exact
  rw [fkRectRawPrimalCrossingBase_torusComponent]
  exact (mem_fkRectRawPrimalCrossingTorusVertices R omega X y).1 hy |>.symm


end
end StatMech.FrontierD
