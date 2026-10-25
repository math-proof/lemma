/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryGeometry
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquarePerimeterEdge (n : Nat)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    FKIsingMedialVertex (fkSquareBoxPlanar n) :=
  fkIsingSquareDirectionEdge n (fkIsingSquareBoundaryVertex n (side, k))
    (fkIsingSquarePerimeterDirection side)
    (fkIsingSquarePerimeterDirection_available n side k)


def fkIsingSquarePerimeterRetainedSide :
    FKIsingSquareBoundarySide → FKIsingMedialSide
  | .bottom => .west
  | .right => .east
  | .top => .east
  | .left => .west


def fkIsingSquarePerimeterCancelledSide :
    FKIsingSquareBoundarySide → FKIsingMedialSide
  | .bottom => .east
  | .right => .west
  | .top => .west
  | .left => .east


def fkIsingSquarePerimeterInteriorSide :
    FKIsingSquareBoundarySide → FKIsingMedialSide
  | .bottom => .west
  | .right => .west
  | .top => .east
  | .left => .east


def fkIsingSquarePerimeterInteriorRadialDart
    (n : Nat) (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fkIsingSquarePerimeterEdge n side k,
      fkIsingSquarePerimeterInteriorSide side), by
    have hk := k.isLt
    cases side <;>
      simp [fkIsingSquarePerimeterInteriorSide,
        fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite] <;> omega⟩


def fkIsingSquarePerimeterInteriorRadialIncidence
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) : FKIsingSquareInteriorRadialIncidence n hn :=
  Quot.mk _ (fkIsingSquarePerimeterInteriorRadialDart n side k)

end
end StatMech.Universality
