/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part3


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def faceSouthWestDart (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(faceSouthEdge n c, .west), by
    rw [show fkIsingSquareWedgeFaceKey n (faceSouthEdge n c, .west) =
        fkIsingSquareInteriorCellKey n c by
      simp [faceSouthEdge, faceSWVertex, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareSideCorner, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]]
    exact fkIsingSquareInteriorCellKey_interior n c⟩

end
end StatMech.Universality
