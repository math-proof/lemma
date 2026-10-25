/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part16


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

def rightBoundaryWestInteriorRadialCell
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    FKIsingSquareInteriorRadialCell n :=
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.right, k1)
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  ⟨fullVertexWestEdge n x hwest, by
    intro s
    fin_cases s <;>
      simp [fullVertexWestEdge, x, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareInteriorFaceKey, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, k1] <;>
      omega⟩


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
