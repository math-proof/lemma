/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part20


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem bottomRightCornerOtherDart_not_boundary
    (n : Nat) (hn : 0 < n) :
    bottomRightCornerOtherDart n hn ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n (bottomRightCornerOtherDart n hn) at hend
  rw [hend] at hwire
  simp [bottomRightCornerOtherDart, bottomRightCornerLast,
    fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hwire
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hwire
  omega

theorem bottomRightCornerOtherDart_bondMate
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn (bottomRightCornerOtherDart n hn) =
      (fkIsingSquarePerimeterEdge n .right (bottomRightCornerZero n hn),
        .west) := by
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
  let d := bottomRightCornerOtherDart n hn
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary n hn d
    (bottomRightCornerOtherDart_not_boundary n hn)]
  have hprevEdge : fkIsingSquareDartEndpoint n d = x := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [d, bottomRightCornerOtherDart, bottomRightCornerLast,
        bottomRightCornerZero, x, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite] <;> omega
  have hdirection : fkIsingSquareDartDirection n d = .west := by
    simp [d, bottomRightCornerOtherDart, bottomRightCornerLast,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
  have hdrepr : d =
      fkIsingSquareDirectionDart n x .west hwest .clockwise := by
    apply fkIsingSquareDart_key_injective n
    simp only [fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction]
    rw [hprevEdge, hdirection]
    simp [d, bottomRightCornerOtherDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
  rw [hdrepr]
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hdir : fkIsingSquarePreviousDirection n x .west = .north := by
    simp [fkIsingSquarePreviousDirection, fkIsingSquareDirectionAvailable, x,
      bottomRightCornerZero, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite]
    omega
  calc
    _ = fkIsingSquareDirectionDart n x .north hnorth .counterclockwise :=
      fkIsingSquareDirectionDart_congr n x hdir _ _ _
    _ = (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .west) := rfl

theorem cornerDart_ne_source_terminal_of_not_boundary
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hd : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    d ≠ fkIsingSquareWiredSourceDart n hn ∧
      d ≠ fkIsingSquareWiredTerminalDart n hn := by
  constructor
  · intro h
    apply hd
    refine ⟨.bottom, ?_⟩
    simpa [fkIsingSquareWiredBoundaryEmbedding,
      fkIsingSquareWiredSourceDart] using h.symm
  · intro h
    apply hd
    refine ⟨.top, ?_⟩
    simpa [fkIsingSquareWiredBoundaryEmbedding,
      fkIsingSquareWiredTerminalDart] using h.symm

theorem bottomRightCornerOtherMate_not_boundary
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquarePerimeterEdge n .right (bottomRightCornerZero n hn),
        .west) ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .west) at hend
  rw [hend] at hwire
  simp [bottomRightCornerZero, fkIsingSquareWiredArc,
    fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
    fkIsingSquareDartEndpoint, fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hwire
  omega

theorem bottomRightCornerCrossDart_ne_source
    (n : Nat) (hn : 0 < n) :
    bottomRightCornerCrossDart n hn ≠ fkIsingSquareWiredSourceDart n hn := by
  intro h
  have hs := congrArg Prod.snd h
  simp [bottomRightCornerCrossDart, fkIsingSquareWiredSourceDart,
    fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
    fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide] at hs

theorem bottomRightCornerCrossDart_ne_terminal
    (n : Nat) (hn : 0 < n) :
    bottomRightCornerCrossDart n hn ≠ fkIsingSquareWiredTerminalDart n hn := by
  intro h
  have hs := congrArg Prod.snd h
  simp [bottomRightCornerCrossDart, fkIsingSquareWiredTerminalDart,
    fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
    fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide] at hs

theorem bottomRightCornerCrossMate_not_boundary
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquarePerimeterEdge n .right (bottomRightCornerZero n hn),
        .south) ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .south) at hend
  rw [hend] at hwire
  simp [bottomRightCornerZero, fkIsingSquareWiredArc,
    fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
    fkIsingSquareDartEndpoint, fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hwire
  omega

theorem bottomRightCornerOtherDart_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (bottomRightCornerOtherDart n hn) =
      bottomRightCornerCrossDart n hn := by
  have hinv := FKIsingMedialDart.localMate_involutive
    (fkIsingSquareClosePerimeter n omega)
    (fkIsingSquarePerimeterEdge n .bottom
      (bottomRightCornerLast n hn), .east)
  have hm : FKIsingMedialDart.localMate
      (fkIsingSquareClosePerimeter n omega)
      (fkIsingSquarePerimeterEdge n .bottom
        (bottomRightCornerLast n hn), .east) =
      (fkIsingSquarePerimeterEdge n .bottom
        (bottomRightCornerLast n hn), .north) := by
    simpa [fkIsingSquareBoundaryLayerComplementInwardSide,
      fkIsingSquareBoundaryLayerComplementEndpointSide] using
      fkIsingSquareBoundaryLayer_complement_localMate n omega .bottom
        (bottomRightCornerLast n hn)
  rw [hm] at hinv
  simpa [bottomRightCornerOtherDart, bottomRightCornerCrossDart,
    fkIsingSquareBoundaryLayerComplementInwardSide,
    fkIsingSquareBoundaryLayerComplementEndpointSide] using hinv

theorem bottomRightCornerCrossDart_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (bottomRightCornerCrossDart n hn) =
      bottomRightCornerOtherDart n hn := by
  simpa [bottomRightCornerOtherDart, bottomRightCornerCrossDart,
    fkIsingSquareBoundaryLayerComplementInwardSide,
    fkIsingSquareBoundaryLayerComplementEndpointSide] using
    fkIsingSquareBoundaryLayer_complement_localMate n omega .bottom
      (bottomRightCornerLast n hn)

theorem bottomRightCornerCrossMate_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (fkIsingSquarePerimeterEdge n .right
          (bottomRightCornerZero n hn), .south) =
      (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .west) := by
  have hinv := FKIsingMedialDart.localMate_involutive
    (fkIsingSquareClosePerimeter n omega)
    (fkIsingSquarePerimeterEdge n .right
      (bottomRightCornerZero n hn), .west)
  have hm : FKIsingMedialDart.localMate
      (fkIsingSquareClosePerimeter n omega)
      (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .west) =
      (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .south) := by
    simpa [fkIsingSquareBoundaryLayerInwardSide,
      fkIsingSquareBoundaryLayerEndpointSide] using
      fkIsingSquareBoundaryLayer_localMate n omega .right
        (bottomRightCornerZero n hn)
  rw [hm] at hinv
  simpa [fkIsingSquareBoundaryLayerInwardSide,
    fkIsingSquareBoundaryLayerEndpointSide] using hinv

theorem bottomRightCornerOtherMate_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (fkIsingSquarePerimeterEdge n .right
          (bottomRightCornerZero n hn), .west) =
      (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .south) := by
  simpa [fkIsingSquareBoundaryLayerInwardSide,
    fkIsingSquareBoundaryLayerEndpointSide] using
    fkIsingSquareBoundaryLayer_localMate n omega .right
      (bottomRightCornerZero n hn)

theorem bottomRightCornerCrossMate_bondMate
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn
        (fkIsingSquarePerimeterEdge n .right
          (bottomRightCornerZero n hn), .south) =
      bottomRightCornerCrossDart n hn := by
  rw [← bottomRightCornerCrossDart_bondMate n hn]
  exact fkIsingSquareWiredBondMate_involutive n hn _

theorem bottomRightCornerOtherMate_bondMate
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn
        (fkIsingSquarePerimeterEdge n .right
          (bottomRightCornerZero n hn), .west) =
      bottomRightCornerOtherDart n hn := by
  rw [← bottomRightCornerOtherDart_bondMate n hn]
  exact fkIsingSquareWiredBondMate_involutive n hn _

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
