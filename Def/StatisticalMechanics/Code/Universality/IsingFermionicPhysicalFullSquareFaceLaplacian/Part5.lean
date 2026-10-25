/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareFaceLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part5


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def faceNorthEastDart (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(faceNorthEdge n c, .east), by
    rw [show fkIsingSquareWedgeFaceKey n (faceNorthEdge n c, .east) =
        fkIsingSquareInteriorCellKey n c by
      rw [faceNorthEdge_eq_west]
      simp [faceNEVertex, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareSideCorner, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]]
    exact fkIsingSquareInteriorCellKey_interior n c⟩

end
end StatMech.Universality
