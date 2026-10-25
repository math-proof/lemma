/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareFaceLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part8


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def faceNorthNeighborDart (n : Nat)
    (c : FKIsingSquareFullFaceNode n) (hnorth : c.2.1 + 1 < 2 * n) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(faceNorthEdge n c, .north), by
    simp [faceNorthEdge, faceNWVertex, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorFaceKey, fkIsingSquareInteriorCellKey] at hnorth ⊢
    have hx := c.1.isLt
    have hy := c.2.isLt
    omega⟩

def faceEastNeighborDart (n : Nat)
    (c : FKIsingSquareFullFaceNode n) (heast : c.1.1 + 1 < 2 * n) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(faceEastEdge n c, .south), by
    simp [faceEastEdge, faceSEVertex, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorFaceKey, fkIsingSquareInteriorCellKey] at heast ⊢
    have hx := c.1.isLt
    have hy := c.2.isLt
    omega⟩

def faceSouthNeighborDart (n : Nat)
    (c : FKIsingSquareFullFaceNode n) (hsouth : 0 < c.2.1) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(faceSouthEdge n c, .south), by
    simp [faceSouthEdge, faceSWVertex, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorFaceKey, fkIsingSquareInteriorCellKey] at hsouth ⊢
    have hx := c.1.isLt
    have hy := c.2.isLt
    omega⟩

def faceWestNeighborDart (n : Nat)
    (c : FKIsingSquareFullFaceNode n) (hwest : 0 < c.1.1) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(faceWestEdge n c, .north), by
    simp [faceWestEdge, faceSWVertex, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorFaceKey, fkIsingSquareInteriorCellKey] at hwest ⊢
    have hx := c.1.isLt
    have hy := c.2.isLt
    omega⟩

end
end StatMech.Universality
