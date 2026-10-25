/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part4


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def faceWestEastDart (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(faceWestEdge n c, .east), by
    rw [show fkIsingSquareWedgeFaceKey n (faceWestEdge n c, .east) =
        fkIsingSquareInteriorCellKey n c by
      rw [faceWestEdge_eq_south]
      simp [faceNWVertex, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareSideCorner, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]]
    exact fkIsingSquareInteriorCellKey_interior n c⟩

end
end StatMech.Universality
