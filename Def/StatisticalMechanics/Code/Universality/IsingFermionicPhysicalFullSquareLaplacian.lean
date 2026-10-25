/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundary.Part3


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fullVertexNorthEdge (n : Nat)
    (x : (fkSquareBoxPlanar n).V)
    (h : fkIsingSquareDirectionAvailable n x .north) :=
  fkIsingSquareDirectionEdge n x .north h

def fullVertexEastEdge (n : Nat)
    (x : (fkSquareBoxPlanar n).V)
    (h : fkIsingSquareDirectionAvailable n x .east) :=
  fkIsingSquareDirectionEdge n x .east h

def fullVertexSouthEdge (n : Nat)
    (x : (fkSquareBoxPlanar n).V)
    (h : fkIsingSquareDirectionAvailable n x .south) :=
  fkIsingSquareDirectionEdge n x .south h

def fullVertexWestEdge (n : Nat)
    (x : (fkSquareBoxPlanar n).V)
    (h : fkIsingSquareDirectionAvailable n x .west) :=
  fkIsingSquareDirectionEdge n x .west h

def northSouthDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (heast : fkIsingSquareDirectionAvailable n x .east) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexNorthEdge n x hnorth, .south), by
    simp [fullVertexNorthEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey,
      fkIsingSquareDirectionAvailable] at heast hnorth ⊢
    have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
    have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
    omega⟩

def eastSouthDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexEastEdge n x heast, .south), by
    simp [fullVertexEastEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey,
      fkIsingSquareDirectionAvailable] at heast hsouth ⊢
    have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
    have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
    omega⟩

def southNorthDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hsouth : fkIsingSquareDirectionAvailable n x .south)
    (hwest : fkIsingSquareDirectionAvailable n x .west) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexSouthEdge n x hsouth, .north), by
    simp [fullVertexSouthEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey,
      fkIsingSquareDirectionAvailable] at hsouth hwest ⊢
    have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
    have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
    omega⟩

def westNorthDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hnorth : fkIsingSquareDirectionAvailable n x .north) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexWestEdge n x hwest, .north), by
    simp [fullVertexWestEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey,
      fkIsingSquareDirectionAvailable] at hwest hnorth ⊢
    have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
    have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
    omega⟩

end
end StatMech.Universality
