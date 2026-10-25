/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def northCenterDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexNorthEdge n x hnorth, .west), by
    simp [fullVertexNorthEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey,
      fkIsingSquareDirectionAvailable] at hnorth hwest ⊢
    have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
    have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
    omega⟩

def northNeighborDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexNorthEdge n x hnorth, .north), by
    rw [show fkIsingSquareWedgeFaceKey n
        (fullVertexNorthEdge n x hnorth, .north) =
      fkIsingSquareWedgeFaceKey n
        (fullVertexNorthEdge n x hnorth, .west) by
      simp [fullVertexNorthEdge, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareSideCorner, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
      constructor <;> rfl]
    exact (northCenterDart n x hnorth hwest).2⟩

def eastCenterDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexEastEdge n x heast, .west), by
    simp [fullVertexEastEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey,
      fkIsingSquareDirectionAvailable] at heast hnorth ⊢
    have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
    have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
    omega⟩

def eastNeighborDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexEastEdge n x heast, .north), by
    rw [show fkIsingSquareWedgeFaceKey n
        (fullVertexEastEdge n x heast, .north) =
      fkIsingSquareWedgeFaceKey n
        (fullVertexEastEdge n x heast, .west) by
      simp [fullVertexEastEdge, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareSideCorner, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
      constructor <;> rfl]
    exact (eastCenterDart n x heast hnorth).2⟩

def southCenterDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hsouth : fkIsingSquareDirectionAvailable n x .south)
    (heast : fkIsingSquareDirectionAvailable n x .east) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexSouthEdge n x hsouth, .east), by
    simp [fullVertexSouthEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey,
      fkIsingSquareDirectionAvailable] at hsouth heast ⊢
    have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
    have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
    omega⟩

def southNeighborDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hsouth : fkIsingSquareDirectionAvailable n x .south)
    (heast : fkIsingSquareDirectionAvailable n x .east) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexSouthEdge n x hsouth, .south), by
    rw [show fkIsingSquareWedgeFaceKey n
        (fullVertexSouthEdge n x hsouth, .south) =
      fkIsingSquareWedgeFaceKey n
        (fullVertexSouthEdge n x hsouth, .east) by
      simp [fullVertexSouthEdge, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareSideCorner, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
      constructor <;> rfl]
    exact (southCenterDart n x hsouth heast).2⟩

def westCenterDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexWestEdge n x hwest, .east), by
    simp [fullVertexWestEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey,
      fkIsingSquareDirectionAvailable] at hwest hsouth ⊢
    have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
    have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
    omega⟩

def westNeighborDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexWestEdge n x hwest, .south), by
    rw [show fkIsingSquareWedgeFaceKey n
        (fullVertexWestEdge n x hwest, .south) =
      fkIsingSquareWedgeFaceKey n
        (fullVertexWestEdge n x hwest, .east) by
      simp [fullVertexWestEdge, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareSideCorner, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
      constructor <;> rfl]
    exact (westCenterDart n x hwest hsouth).2⟩

end
end StatMech.Universality
