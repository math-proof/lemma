/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part23


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem topRightCornerOtherDart_not_boundary
    (n : Nat) (hn : 0 < n) :
    topRightCornerOtherDart n hn ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n (topRightCornerOtherDart n hn) at hend
  rw [hend] at hwire
  simp [topRightCornerOtherDart, bottomRightCornerLast,
    fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hwire
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hwire
  omega

theorem topRightCornerOtherDart_bondMate
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn (topRightCornerOtherDart n hn) =
      (fkIsingSquarePerimeterEdge n .top (bottomRightCornerZero n hn),
        .north) := by
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
  let d := topRightCornerOtherDart n hn
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary n hn d
    (topRightCornerOtherDart_not_boundary n hn)]
  have hprevEdge : fkIsingSquareDartEndpoint n d = x := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [d, topRightCornerOtherDart, bottomRightCornerLast,
        bottomRightCornerZero, x, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite] <;> omega
  have hdirection : fkIsingSquareDartDirection n d = .south := by
    simp [d, topRightCornerOtherDart, bottomRightCornerLast,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
  have hdrepr : d =
      fkIsingSquareDirectionDart n x .south hsouth .counterclockwise := by
    apply fkIsingSquareDart_key_injective n
    simp only [fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction]
    rw [hprevEdge, hdirection]
    simp [d, topRightCornerOtherDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
  rw [hdrepr]
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hdir : fkIsingSquareNextDirection n x .south = .west := by
    simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable, x,
      bottomRightCornerZero, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite]
  calc
    _ = fkIsingSquareDirectionDart n x .west hwest .clockwise :=
      fkIsingSquareDirectionDart_congr n x hdir _ _ _
    _ = (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .north) := rfl

theorem topRightCornerCrossMate_not_boundary
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquarePerimeterEdge n .top (bottomRightCornerZero n hn),
        .east) ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .east) at hend
  rw [hend] at hwire
  simp [bottomRightCornerZero, fkIsingSquareWiredArc,
    fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
    fkIsingSquareDartEndpoint, fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hwire
  omega

theorem topRightCornerOtherMate_not_boundary
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquarePerimeterEdge n .top (bottomRightCornerZero n hn),
        .north) ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .north) at hend
  rw [hend] at hwire
  simp [bottomRightCornerZero, fkIsingSquareWiredArc,
    fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
    fkIsingSquareDartEndpoint, fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hwire
  omega

theorem topRightCornerOtherDart_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (topRightCornerOtherDart n hn) =
      topRightCornerCrossDart n hn := by
  simpa [topRightCornerOtherDart, topRightCornerCrossDart,
    fkIsingSquareBoundaryLayerComplementInwardSide,
    fkIsingSquareBoundaryLayerComplementEndpointSide] using
    fkIsingSquareBoundaryLayer_complement_localMate n omega .right
      (bottomRightCornerLast n hn)

theorem topRightCornerCrossDart_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (topRightCornerCrossDart n hn) =
      topRightCornerOtherDart n hn := by
  have hinv := FKIsingMedialDart.localMate_involutive
    (fkIsingSquareClosePerimeter n omega)
    (topRightCornerOtherDart n hn)
  rw [topRightCornerOtherDart_localMate n hn omega] at hinv
  exact hinv

theorem topRightCornerCrossMate_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (fkIsingSquarePerimeterEdge n .top
          (bottomRightCornerZero n hn), .east) =
      (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .north) := by
  simpa [fkIsingSquareBoundaryLayerInwardSide,
    fkIsingSquareBoundaryLayerEndpointSide] using
    fkIsingSquareBoundaryLayer_localMate n omega .top
      (bottomRightCornerZero n hn)

theorem topRightCornerOtherMate_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (fkIsingSquarePerimeterEdge n .top
          (bottomRightCornerZero n hn), .north) =
      (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .east) := by
  have hinv := FKIsingMedialDart.localMate_involutive
    (fkIsingSquareClosePerimeter n omega)
    (fkIsingSquarePerimeterEdge n .top
      (bottomRightCornerZero n hn), .east)
  have hm := topRightCornerCrossMate_localMate n hn omega
  rw [hm] at hinv
  exact hinv

theorem topRightCornerCrossMate_bondMate
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn
        (fkIsingSquarePerimeterEdge n .top
          (bottomRightCornerZero n hn), .east) =
      topRightCornerCrossDart n hn := by
  rw [← topRightCornerCrossDart_bondMate n hn]
  exact fkIsingSquareWiredBondMate_involutive n hn _

theorem topRightCornerOtherMate_bondMate
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn
        (fkIsingSquarePerimeterEdge n .top
          (bottomRightCornerZero n hn), .north) =
      topRightCornerOtherDart n hn := by
  rw [← topRightCornerOtherDart_bondMate n hn]
  exact fkIsingSquareWiredBondMate_involutive n hn _

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
