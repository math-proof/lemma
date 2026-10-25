/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part22


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem topRightCornerCrossDart_not_boundary
    (n : Nat) (hn : 0 < n) :
    topRightCornerCrossDart n hn ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n (topRightCornerCrossDart n hn) at hend
  rw [hend] at hwire
  simp [topRightCornerCrossDart, bottomRightCornerLast,
    fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hwire
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hwire
  omega

theorem topRightCornerCrossDart_bondMate
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn (topRightCornerCrossDart n hn) =
      (fkIsingSquarePerimeterEdge n .top (bottomRightCornerZero n hn),
        .east) := by
  let x := fkIsingSquareBoundaryVertex n
    (.top, bottomRightCornerZero n hn)
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let d := topRightCornerCrossDart n hn
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary n hn d
    (topRightCornerCrossDart_not_boundary n hn)]
  have hprevEdge : fkIsingSquareDartEndpoint n d = x := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [d, topRightCornerCrossDart, bottomRightCornerLast,
        bottomRightCornerZero, x, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite] <;> omega
  have hdirection : fkIsingSquareDartDirection n d = .south := by
    simp [d, topRightCornerCrossDart, bottomRightCornerLast,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
  have hdrepr : d =
      fkIsingSquareDirectionDart n x .south hsouth .clockwise := by
    apply fkIsingSquareDart_key_injective n
    simp only [fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction]
    rw [hprevEdge, hdirection]
    simp [d, topRightCornerCrossDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
  rw [hdrepr]
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hdir : fkIsingSquarePreviousDirection n x .south = .west := by
    simp [fkIsingSquarePreviousDirection, fkIsingSquareDirectionAvailable, x,
      bottomRightCornerZero, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite]
    omega
  calc
    _ = fkIsingSquareDirectionDart n x .west hwest .counterclockwise :=
      fkIsingSquareDirectionDart_congr n x hdir _ _ _
    _ = (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .east) := rfl

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
