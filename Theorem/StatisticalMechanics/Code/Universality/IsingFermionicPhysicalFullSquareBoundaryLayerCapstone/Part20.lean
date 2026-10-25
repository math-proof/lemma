/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part19


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem bottomRightCornerCrossDart_not_boundary
    (n : Nat) (hn : 0 < n) :
    bottomRightCornerCrossDart n hn ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n (bottomRightCornerCrossDart n hn) at hend
  rw [hend] at hwire
  simp [bottomRightCornerCrossDart, bottomRightCornerLast,
    fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hwire
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hwire
  omega

theorem bottomRightCornerCrossDart_bondMate
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn (bottomRightCornerCrossDart n hn) =
      (fkIsingSquarePerimeterEdge n .right (bottomRightCornerZero n hn),
        .south) := by
  let x := fkIsingSquareBoundaryVertex n
    (.right, bottomRightCornerZero n hn)
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let d := bottomRightCornerCrossDart n hn
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary n hn d
    (bottomRightCornerCrossDart_not_boundary n hn)]
  have hprevEdge : fkIsingSquareDartEndpoint n d = x := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [d, bottomRightCornerCrossDart, bottomRightCornerLast,
        bottomRightCornerZero, x, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite] <;> omega
  have hdirection : fkIsingSquareDartDirection n d = .west := by
    simp [d, bottomRightCornerCrossDart, bottomRightCornerLast,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
  have hdrepr : d =
      fkIsingSquareDirectionDart n x .west hwest .counterclockwise := by
    apply fkIsingSquareDart_key_injective n
    simp only [fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction]
    rw [hprevEdge, hdirection]
    simp [d, bottomRightCornerCrossDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
  rw [hdrepr]
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hdir : fkIsingSquareNextDirection n x .west = .north := by
    simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable, x,
      bottomRightCornerZero, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite]
  calc
    _ = fkIsingSquareDirectionDart n x .north hnorth .clockwise :=
      fkIsingSquareDirectionDart_congr n x hdir _ _ _
    _ = (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .south) := rfl

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
