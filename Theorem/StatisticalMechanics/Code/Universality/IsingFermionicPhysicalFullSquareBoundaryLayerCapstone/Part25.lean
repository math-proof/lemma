/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part24


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem topRightCornerCycleCarrier_of_adj
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hx : topRightCornerCycleCarrier n hn x)
    (hxy : (fkIsingSquareWiredLoopGraph n hn
      (fkIsingSquareClosePerimeter n omega)).Adj x y) :
    topRightCornerCycleCarrier n hn y := by
  have hother := cornerDart_ne_source_terminal_of_not_boundary n hn
    (topRightCornerOtherDart n hn)
    (topRightCornerOtherDart_not_boundary n hn)
  have hcross := cornerDart_ne_source_terminal_of_not_boundary n hn
    (topRightCornerCrossDart n hn)
    (topRightCornerCrossDart_not_boundary n hn)
  have hcrossMate := cornerDart_ne_source_terminal_of_not_boundary n hn
    (fkIsingSquarePerimeterEdge n .top
      (bottomRightCornerZero n hn), .east)
    (topRightCornerCrossMate_not_boundary n hn)
  have hotherMate := cornerDart_ne_source_terminal_of_not_boundary n hn
    (fkIsingSquarePerimeterEdge n .top
      (bottomRightCornerZero n hn), .north)
    (topRightCornerOtherMate_not_boundary n hn)
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hxy with ⟨-, -, rfl⟩ | rfl <;>
    simp [topRightCornerCycleCarrier,
      fkIsingSquareWiredIncidenceMate, fkIsingSquareWiredTransitionMate,
      topRightCornerOtherDart_localMate,
      topRightCornerCrossDart_localMate,
      topRightCornerCrossMate_localMate,
      topRightCornerOtherMate_localMate,
      topRightCornerCrossDart_bondMate,
      topRightCornerCrossMate_bondMate,
      topRightCornerOtherDart_bondMate,
      topRightCornerOtherMate_bondMate,
      hother.1, hother.2, hcross.1, hcross.2,
      hcrossMate.1, hcrossMate.2, hotherMate.1, hotherMate.2]

theorem topRightCornerCycleCarrier_not_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {z : FKIsingSquareWiredCarrier n}
    (hz : topRightCornerCycleCarrier n hn z) :
    ¬ (fkIsingSquareWiredLoopGraph n hn
      (fkIsingSquareClosePerimeter n omega)).Reachable .source z := by
  intro hreach
  obtain ⟨p⟩ := hreach.symm
  have htransport : ∀ {a b : FKIsingSquareWiredCarrier n},
      (fkIsingSquareWiredLoopGraph n hn
        (fkIsingSquareClosePerimeter n omega)).Walk a b →
      topRightCornerCycleCarrier n hn a →
      topRightCornerCycleCarrier n hn b := by
    intro a b q
    induction q with
    | nil => exact fun ha => ha
    | cons hadj q ih =>
        intro ha
        exact ih (topRightCornerCycleCarrier_of_adj n hn omega ha hadj)
  have hsource := htransport p hz
  simpa [topRightCornerCycleCarrier] using hsource

theorem topRightCornerCrossMate_not_mem_exploration
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace
      (Sym2 (fkIsingSquareBoundaryDeletedPlanar n).V)) :
    (.dart (fkIsingSquarePerimeterEdge n .top
      (bottomRightCornerZero n hn), .east) : FKIsingSquareWiredCarrier n) ∉
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration omega := by
  change (.dart (fkIsingSquarePerimeterEdge n .top
      (bottomRightCornerZero n hn), .east) : FKIsingSquareWiredCarrier n) ∉
    fkIsingSquareWiredExplorationOrder n hn
      (fkIsingSquareClosePerimeter n omega)
  rw [mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
  apply topRightCornerCycleCarrier_not_reachable n hn omega
  simp [topRightCornerCycleCarrier]


theorem topRightCorner_inward_observable_eq_zero
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .east)) = 0 := by
  unfold FKIsingDobrushinDomain.fermionicObservable
  apply Finset.sum_eq_zero
  intro omega _
  unfold FKIsingDobrushinDomain.fermionicSummand
  rw [if_neg (topRightCornerCrossMate_not_mem_exploration n hn omega)]


theorem topRightCorner_inward_increment_eq_zero
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .east)) = 0 := by
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [topRightCorner_inward_observable_eq_zero n hn]
  exact Complex.normSq_zero

theorem topRightCornerCrossDart_ne_source
    (n : Nat) (hn : 0 < n) :
    topRightCornerCrossDart n hn ≠ fkIsingSquareWiredSourceDart n hn := by
  intro h
  have he := congrArg
    (fun d => (fkIsingSquareDartEndpoint n d).1 0) h
  simp [topRightCornerCrossDart, bottomRightCornerLast,
    fkIsingSquareWiredSourceDart, fkIsingSquareWiredBoundaryDart,
    fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
    fkIsingSquareCornerSide, fkIsingSquareDartEndpoint,
    fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
    fkIsingSquareMarkedA, fkIsingSquareNeighbor,
    fkIsingSquareNeighborSite] at he
  omega

theorem topRightCornerCrossDart_ne_terminal
    (n : Nat) (hn : 0 < n) :
    topRightCornerCrossDart n hn ≠ fkIsingSquareWiredTerminalDart n hn := by
  intro h
  have he := congrArg
    (fun d => (fkIsingSquareDartEndpoint n d).1 0) h
  simp [topRightCornerCrossDart, bottomRightCornerLast,
    fkIsingSquareWiredTerminalDart, fkIsingSquareWiredBoundaryDart,
    fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
    fkIsingSquareCornerSide, fkIsingSquareDartEndpoint,
    fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
    fkIsingSquareMarkedB, fkIsingSquareNeighbor,
    fkIsingSquareNeighborSite] at he
  omega


theorem topRightCorner_inward_increment_eq
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .right
          (bottomRightCornerLast n hn), .east)) =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .top
          (bottomRightCornerZero n hn), .east)) := by
  let d := topRightCornerCrossDart n hn
  have hbond := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate n hn d
    (topRightCornerCrossDart_ne_source n hn)
    (topRightCornerCrossDart_ne_terminal n hn)
  rw [topRightCornerCrossDart_bondMate n hn] at hbond
  have hright :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .right (bottomRightCornerLast n hn)
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerLast n hn), .east)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerLast n hn), .north)) at hright
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .east)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerLast n hn), .north)) at hbond
  exact hright.trans hbond.symm


theorem topRightCorner_vertex_difference_south
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    let zero := bottomRightCornerZero n hn
    let x0 := fkIsingSquareBoundaryVertex n (.right, last)
    let x1 := fkIsingSquareBoundaryVertex n (.top, zero)
    let e := fkIsingSquarePerimeterEdge n .right last
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x0 -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x1 =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south)) := by
  let last := bottomRightCornerLast n hn
  let zero := bottomRightCornerZero n hn
  let x0 := fkIsingSquareBoundaryVertex n (.right, last)
  let x1 := fkIsingSquareBoundaryVertex n (.top, zero)
  let ep := fkIsingSquarePerimeterEdge n .right last
  let d0 : FKIsingSquareInteriorRadialDart n := ⟨(ep, .west), by
    simp [ep, last, bottomRightCornerLast, fkIsingSquareWedgeFaceKey,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey]
    omega⟩
  let d1 : FKIsingSquareInteriorRadialDart n := ⟨(ep, .north), by
    simp [ep, last, bottomRightCornerLast, fkIsingSquareWedgeFaceKey,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey]
    omega⟩
  let r0 : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d0
  let r1 : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d1
  have hend0 : fkIsingSquareInteriorRadialEndpoint n hn r0 = x0 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [r0, d0, ep, x0, last, bottomRightCornerLast,
        fkIsingSquareInteriorRadialEndpoint, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
  have hend1 : fkIsingSquareInteriorRadialEndpoint n hn r1 = x1 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [r1, d1, ep, x1, last, zero, bottomRightCornerLast,
        bottomRightCornerZero, fkIsingSquareInteriorRadialEndpoint,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareSideCorner,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;> omega
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn r0 =
      fkIsingSquareFullFaceOfRadialIncidence n hn r1 := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [r0, r1, d0, d1, ep, last, bottomRightCornerLast,
      fkIsingSquareWedgeFaceKey, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
  have h0 :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn r0
  have h1 :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn r1
  rw [hend0, hface] at h0
  rw [hend1] at h1
  change _ = fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (ep, .west)) at h0
  change _ = fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (ep, .north)) at h1
  have hstd := fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    n hn .right last
  have hcomp :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .right last
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .west)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .south)) at hstd
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .east)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .north)) at hcomp
  linarith


theorem topRightCorner_vertex_laplacian_eq_increment_divergence
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    let zero := bottomRightCornerZero n hn
    let x := fkIsingSquareBoundaryVertex n (.top, zero)
    let eS := fkIsingSquarePerimeterEdge n .right last
    let eW := fkIsingSquarePerimeterEdge n .top zero
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .east)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .south))) +
        (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .east)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .south))) := by
  let last := bottomRightCornerLast n hn
  let zero := bottomRightCornerZero n hn
  let x := fkIsingSquareBoundaryVertex n (.top, zero)
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, zero, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, zero, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let xS := fkIsingSquareNeighbor n x .south hsouth
  let xW := fkIsingSquareNeighbor n x .west hwest
  let eS := fkIsingSquarePerimeterEdge n .right last
  let eW := fkIsingSquarePerimeterEdge n .top zero
  let H := (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
  have hneighbors : (fkSquareBoxPlanar n).G.neighborFinset x = {xS, xW} := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hxy
      change (hypercubicLattice 2).Adj x.1 y.1 at hxy
      rcases adj_neighbor_cases x.1 y.1 hxy with h | h | h | h
      · right
        apply Subtype.ext
        funext i
        fin_cases i
        · have hi := congrFun h 0
          simp [Pi.add_apply] at hi
          change y.1 0 = x.1 0 - 1
          omega
        · have hi := congrFun h 1
          simp [Pi.add_apply] at hi
          simpa [xW, fkIsingSquareNeighbor,
            fkIsingSquareNeighborSite] using hi.symm
      · have hi := congrFun h 0
        simp [Pi.add_apply, x, zero, bottomRightCornerZero,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hi
        have hy := fkIsingSquareVertex_coordinate_bounds n y 0
        omega
      · left
        apply Subtype.ext
        funext i
        fin_cases i
        · have hi := congrFun h 0
          simp [Pi.add_apply] at hi
          simpa [xS, fkIsingSquareNeighbor,
            fkIsingSquareNeighborSite] using hi.symm
        · have hi := congrFun h 1
          simp [Pi.add_apply] at hi
          change y.1 1 = x.1 1 - 1
          omega
      · have hi := congrFun h 1
        simp [Pi.add_apply, x, zero, bottomRightCornerZero,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hi
        have hy := fkIsingSquareVertex_coordinate_bounds n y 1
        omega
    · rintro (rfl | rfl)
      · exact fkIsingSquare_adj_neighbor n x .south hsouth
      · exact fkIsingSquare_adj_neighbor n x .west hwest
  have hSW : xS ≠ xW := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) h
    simp [xS, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hLap : isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x =
      (H xS - H x) + (H xW - H x) := by
    unfold isingFiniteGraphLaplacian
    rw [hneighbors]
    simp [hSW]
    ring
  have hdS := topRightCorner_vertex_difference_south n hn
  have hdW := vertex_difference_west n hn x hwest hsouth
  change H xW - H x = _ at hdW
  have hx0 : fkIsingSquareBoundaryVertex n (.right, last) = xS := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [xS, x, last, zero, bottomRightCornerLast,
        bottomRightCornerZero, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite] <;> omega
  change H (fkIsingSquareBoundaryVertex n (.right, last)) - H x = _ at hdS
  rw [hx0] at hdS
  have heW : fullVertexWestEdge n x hwest = eW := by rfl
  rw [heW] at hdW
  rw [show fkIsingSquarePerimeterEdge n .right last = eS by rfl] at hdS
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x = _
  rw [hLap, hdS, hdW]

theorem topRightCorner_vertex_laplacian_eq_corner_divergence
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    let zero := bottomRightCornerZero n hn
    let x := fkIsingSquareBoundaryVertex n (.top, zero)
    let a := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right last, .south))
    let b := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .top zero, .east))
    let d := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .top zero, .south))
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      (b - a) + (b - d) := by
  dsimp only
  rw [topRightCorner_vertex_laplacian_eq_increment_divergence n hn]
  rw [topRightCorner_inward_increment_eq n hn]

theorem vertex_modifiedLaplacian_nonpos_of_topRightCorner_of_increment_bound
    (n : Nat) (hn : 0 < n)
    (hcorner :
      let last := bottomRightCornerLast n hn
      let zero := bottomRightCornerZero n hn
      let a := fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .right last, .south))
      let b := fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .top zero, .east))
      let d := fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .top zero, .south))
      2 * (1 + isingFermionicGhostCoefficient) * b ≤ a + d) :
    let zero := bottomRightCornerZero n hn
    let x := fkIsingSquareBoundaryVertex n (.top, zero)
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
      ≤ 0 := by
  let last := bottomRightCornerLast n hn
  let zero := bottomRightCornerZero n hn
  let x := fkIsingSquareBoundaryVertex n (.top, zero)
  let a := fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .right last, .south))
  let b := fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .top zero, .east))
  let d := fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .top zero, .south))
  have hlap := topRightCorner_vertex_laplacian_eq_corner_divergence n hn
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
        (b - a) + (b - d) at hlap
  have hgap := boundaryLayer_inwardIncrement_eq_one_sub_vertex
    n hn .top zero (by decide)
  change b = 1 -
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x at hgap
  have hmult : fkIsingSquareFullVertexGhostMultiplicity n x = 2 := by
    simp [fkIsingSquareFullVertexGhostMultiplicity, x, zero,
      bottomRightCornerZero, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite]
    omega
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
      isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x *
          (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
    ≤ 0
  rw [hlap, ← hgap, isingFermionicGhostRate, hmult]
  dsimp only [Nat.cast_ofNat]
  change (b - a) + (b - d) +
    (isingFermionicGhostCoefficient * 2) * b ≤ 0
  have hc : 2 * (1 + isingFermionicGhostCoefficient) * b ≤ a + d := hcorner
  nlinarith


theorem topRightCorner_increment_bound
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    let zero := bottomRightCornerZero n hn
    let a := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right last, .south))
    let b := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .top zero, .east))
    let d := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .top zero, .south))
    2 * (1 + isingFermionicGhostCoefficient) * b ≤ a + d := by
  dsimp only
  rw [topRightCorner_inward_increment_eq_zero n hn]
  have ha := isingPrimitiveIncrement_nonneg
    ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerLast n hn), .south)))
  have hd := isingPrimitiveIncrement_nonneg
    ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .south)))
  change 0 ≤ fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .right
      (bottomRightCornerLast n hn), .south)) at ha
  change 0 ≤ fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .top
      (bottomRightCornerZero n hn), .south)) at hd
  nlinarith


theorem vertex_modifiedLaplacian_nonpos_of_topRightCorner
    (n : Nat) (hn : 0 < n) :
    let zero := bottomRightCornerZero n hn
    let x := fkIsingSquareBoundaryVertex n (.top, zero)
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
      ≤ 0 := by
  apply vertex_modifiedLaplacian_nonpos_of_topRightCorner_of_increment_bound
  exact topRightCorner_increment_bound n hn

theorem bottomRightCorner_ghostMultiplicity
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareFullVertexGhostMultiplicity n
        (fkIsingSquareBoundaryVertex n
          (.right, bottomRightCornerZero n hn)) = 2 := by
  simp [fkIsingSquareFullVertexGhostMultiplicity, bottomRightCornerZero,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
  omega

theorem topRightCorner_ghostMultiplicity
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareFullVertexGhostMultiplicity n
        (fkIsingSquareBoundaryVertex n
          (.top, bottomRightCornerZero n hn)) = 2 := by
  simp [fkIsingSquareFullVertexGhostMultiplicity, bottomRightCornerZero,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
  omega


theorem cornerIncrementDivergence_add_ghost_nonpos
    (far₁ near far₂ : Real)
    (hcorner : 2 * (1 + isingFermionicGhostCoefficient) * near ≤
      far₁ + far₂) :
    (near - far₁) + (near - far₂) +
        2 * isingFermionicGhostCoefficient * near ≤ 0 := by
  linarith


theorem vertex_modifiedLaplacian_nonpos_of_bottomBoundary
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
      ≤ 0 := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
  change isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
      isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x *
          (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
    ≤ 0
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let eN := fullVertexNorthEdge n x hnorth
  let north := fkIsingSquareBoundaryFullMedialObservable n hn eN
  let east := fkIsingSquareBottomBoundaryMedialObservable n hn k1
  let south := fkIsingSquareBottomBoundaryMissingSouthObservable n hn k
  let west := fkIsingSquareBottomBoundaryMedialObservable n hn k0
  have hquad : IsingSquareSHolomorphicQuad south west north east := by
    simpa [south, west, north, east, eN, x, k0, k1] using
      fkIsingSquareBottomBoundaryObservable_quad n hn k
  obtain ⟨hNE, hWN⟩ :=
    isingSquareSHolomorphicQuad_bottom_projection_cycle
      south west north east hquad
  have hphase : isingProj (-Complex.I) north =
      -isingLambda * isingProj 1 north := by
    calc
      isingProj (-Complex.I) north = isingProj (-Complex.I) west := hWN.symm
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .north)) := by
        simpa [west] using
          fkIsingSquareBottomBoundaryMedialObservable_projection_north
            n hn k0
      _ = -isingLambda *
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (fkIsingSquarePerimeterEdge n .bottom k1, .west)) := by
        simpa [k0, k1] using bottom_boundary_inward_observable_phase n hn k
      _ = -isingLambda * isingProj 1 east := by
        rw [fkIsingSquareBottomBoundaryMedialObservable_projection_west]
      _ = -isingLambda * isingProj 1 north := by rw [← hNE]
  have hdiv :=
    isingPrimalProjectionDivergenceWithoutSouth_bottom_add_ghost_nonpos
      north east west hNE hWN hphase
  have hgap := boundaryLayer_inwardIncrement_eq_one_sub_vertex
    n hn .bottom k1 (by decide)
  have hproj : Complex.normSq (isingProj 1 north) =
      1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x := by
    rw [hNE]
    rw [fkIsingSquareBottomBoundaryMedialObservable_projection_west]
    simpa [fkIsingSquareBoundaryLayerInwardIncrement, x, east] using hgap
  have hlap :=
    bottom_boundary_vertex_laplacian_eq_projectionDivergenceWithoutSouth n hn k
  have hs : x.1 1 = -(n : Int) := by
    simp [x, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
  have he : x.1 0 ≠ (n : Int) := by
    simp [x, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    have hk := k.isLt
    omega
  have hmult : fkIsingSquareFullVertexGhostMultiplicity n x = 1 := by
    simp [fkIsingSquareFullVertexGhostMultiplicity, hs, he,
      Nat.ne_of_gt hn]
  have hrate : isingFermionicGhostRate
      (fkIsingSquareFullVertexGhostMultiplicity n) x =
        isingFermionicGhostCoefficient := by
    simp [isingFermionicGhostRate, hmult]
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
      isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x *
          (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
    ≤ 0
  rw [hlap, hrate, ← hproj]
  exact hdiv


theorem vertex_modifiedLaplacian_nonpos_of_rightBoundary
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.right, k1)
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
      ≤ 0 := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.right, k1)
  change isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
      isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x *
          (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
    ≤ 0
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let eW := fullVertexWestEdge n x hwest
  let north := fkIsingSquareRightBoundaryMedialObservable n hn k1
  let south := fkIsingSquareRightBoundaryMedialObservable n hn k0
  let west := fkIsingSquareBoundaryFullMedialObservable n hn eW
  obtain ⟨hSW, hWN⟩ := right_boundary_projection_cycle n hn k
  have hphase : isingProj (-1) west =
      -isingLambda * isingProj (-Complex.I) west := by
    calc
      isingProj (-1) west = isingProj (-1) south := hSW.symm
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .right k0, .north)) := by
        simpa [south] using
          fkIsingSquareRightBoundaryMedialObservable_projection_north
            n hn k0
      _ = -isingLambda *
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (fkIsingSquarePerimeterEdge n .right k1, .west)) := by
        simpa [k0, k1] using right_boundary_inward_observable_phase n hn k
      _ = -isingLambda * isingProj (-Complex.I) north := by
        rw [fkIsingSquareRightBoundaryMedialObservable_projection_west]
      _ = -isingLambda * isingProj (-Complex.I) west := by rw [hWN]
  have hdiv :=
    isingPrimalProjectionDivergenceWithoutEast_right_add_ghost_nonpos
      north south west hSW hWN hphase
  have hgap := boundaryLayer_inwardIncrement_eq_one_sub_vertex
    n hn .right k1 (by decide)
  have hproj : Complex.normSq (isingProj (-Complex.I) west) =
      1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x := by
    rw [hWN]
    rw [fkIsingSquareRightBoundaryMedialObservable_projection_west]
    simpa [fkIsingSquareBoundaryLayerInwardIncrement, x, north] using hgap
  have hlap :=
    right_boundary_vertex_laplacian_eq_projectionDivergenceWithoutEast n hn k
  have hmult : fkIsingSquareFullVertexGhostMultiplicity n x = 1 := by
    unfold fkIsingSquareFullVertexGhostMultiplicity
    simp [x, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    have hk := k.isLt
    split_ifs <;> omega
  have hrate : isingFermionicGhostRate
      (fkIsingSquareFullVertexGhostMultiplicity n) x =
        isingFermionicGhostCoefficient := by
    simp [isingFermionicGhostRate, hmult]
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
      isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x *
          (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
    ≤ 0
  rw [hlap, hrate, ← hproj]
  exact hdiv


theorem vertex_modifiedLaplacian_nonpos_of_topBoundary
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.top, k1)
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
      ≤ 0 := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.top, k1)
  change isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
      isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x *
          (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
    ≤ 0
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let eS := fullVertexSouthEdge n x hsouth
  let east := fkIsingSquareTopBoundaryMedialObservable n hn k0
  let south := fkIsingSquareBoundaryFullMedialObservable n hn eS
  let west := fkIsingSquareTopBoundaryMedialObservable n hn k1
  obtain ⟨hES, hSW⟩ := top_boundary_projection_cycle n hn k
  have hphase : isingProj Complex.I south =
      -isingLambda * isingProj (-1) south := by
    calc
      isingProj Complex.I south = isingProj Complex.I east := hES.symm
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .top k0, .south)) := by
        simpa [east] using
          fkIsingSquareTopBoundaryMedialObservable_projection_south
            n hn k0
      _ = -isingLambda *
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (fkIsingSquarePerimeterEdge n .top k1, .east)) := by
        simpa [k0, k1] using top_boundary_inward_observable_phase n hn k
      _ = -isingLambda * isingProj (-1) west := by
        rw [fkIsingSquareTopBoundaryMedialObservable_projection_east]
      _ = -isingLambda * isingProj (-1) south := by rw [hSW]
  have hdiv :=
    isingPrimalProjectionDivergenceWithoutNorth_top_add_ghost_nonpos
      east south west hES hSW hphase
  have hgap := boundaryLayer_inwardIncrement_eq_one_sub_vertex
    n hn .top k1 (by decide)
  have hproj : Complex.normSq (isingProj (-1) south) =
      1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x := by
    rw [hSW]
    rw [fkIsingSquareTopBoundaryMedialObservable_projection_east]
    simpa [fkIsingSquareBoundaryLayerInwardIncrement, x, west] using hgap
  have hlap :=
    top_boundary_vertex_laplacian_eq_projectionDivergenceWithoutNorth n hn k
  have hmult : fkIsingSquareFullVertexGhostMultiplicity n x = 1 := by
    unfold fkIsingSquareFullVertexGhostMultiplicity
    simp [x, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    have hk := k.isLt
    omega
  have hrate : isingFermionicGhostRate
      (fkIsingSquareFullVertexGhostMultiplicity n) x =
        isingFermionicGhostCoefficient := by
    simp [isingFermionicGhostRate, hmult]
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
      isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x *
          (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
    ≤ 0
  rw [hlap, hrate, ← hproj]
  exact hdiv


theorem vertex_modifiedLaplacian_nonpos_of_interior
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareFullVertexNode n)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
      <= 0 := by
  have hmult : fkIsingSquareFullVertexGhostMultiplicity n x = 0 := by
    unfold fkIsingSquareFullVertexGhostMultiplicity
    simp [fkIsingSquareDirectionAvailable] at heast hnorth hwest hsouth
    split_ifs <;> omega
  rw [show fkIsingSquareFullVertexGraph n = (fkSquareBoxPlanar n).G from rfl]
  simp [isingFermionicGhostRate, hmult]
  exact vertex_laplacian_nonpos_of_interior n hn x
    heast hnorth hwest hsouth


theorem vertex_modifiedLaplacian_nonpos_of_not_wiredArc
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareFullVertexNode n)
    (hxFree : ¬ fkIsingSquareWiredArc n x) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
      ≤ 0 := by
  have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
  have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
  have hxLeft : x.1 0 ≠ -(n : Int) := by
    simpa [fkIsingSquareWiredArc] using hxFree
  by_cases hbottom : x.1 1 = -(n : Int)
  · by_cases hright : x.1 0 = (n : Int)
    · have hx : x = fkIsingSquareBoundaryVertex n
          (.right, bottomRightCornerZero n hn) := by
        apply Subtype.ext
        funext i
        fin_cases i <;>
          simp [bottomRightCornerZero, fkIsingSquareBoundaryVertex,
            fkIsingSquareBoundarySite, hbottom, hright]
      rw [hx]
      exact vertex_modifiedLaplacian_nonpos_of_bottomRightCorner n hn
    · let j : Nat := Int.toNat (x.1 0 + (n : Int))
      have hj0 : 0 ≤ x.1 0 + (n : Int) := by omega
      have hj : (j : Int) = x.1 0 + (n : Int) := by
        simpa [j] using Int.toNat_of_nonneg hj0
      have hjLower : 1 ≤ j := by omega
      have hjUpper : j < 2 * n := by omega
      let k : Fin (2 * n - 1) := ⟨j - 1, by omega⟩
      let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
      have hx : x = fkIsingSquareBoundaryVertex n (.bottom, k1) := by
        apply Subtype.ext
        funext i
        fin_cases i <;>
          simp [k1, k, fkIsingSquareBoundaryVertex,
            fkIsingSquareBoundarySite, hbottom] <;> omega
      rw [hx]
      exact vertex_modifiedLaplacian_nonpos_of_bottomBoundary n hn k
  · by_cases hright : x.1 0 = (n : Int)
    · by_cases htop : x.1 1 = (n : Int)
      · have hx : x = fkIsingSquareBoundaryVertex n
            (.top, bottomRightCornerZero n hn) := by
          apply Subtype.ext
          funext i
          fin_cases i <;>
            simp [bottomRightCornerZero, fkIsingSquareBoundaryVertex,
              fkIsingSquareBoundarySite, hright, htop]
        rw [hx]
        exact vertex_modifiedLaplacian_nonpos_of_topRightCorner n hn
      · let j : Nat := Int.toNat (x.1 1 + (n : Int))
        have hj0 : 0 ≤ x.1 1 + (n : Int) := by omega
        have hj : (j : Int) = x.1 1 + (n : Int) := by
          simpa [j] using Int.toNat_of_nonneg hj0
        have hjLower : 1 ≤ j := by omega
        have hjUpper : j < 2 * n := by omega
        let k : Fin (2 * n - 1) := ⟨j - 1, by omega⟩
        let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
        have hx : x = fkIsingSquareBoundaryVertex n (.right, k1) := by
          apply Subtype.ext
          funext i
          fin_cases i <;>
            simp [k1, k, fkIsingSquareBoundaryVertex,
              fkIsingSquareBoundarySite, hright] <;> omega
        rw [hx]
        exact vertex_modifiedLaplacian_nonpos_of_rightBoundary n hn k
    · by_cases htop : x.1 1 = (n : Int)
      · let j : Nat := Int.toNat ((n : Int) - x.1 0)
        have hj0 : 0 ≤ (n : Int) - x.1 0 := by omega
        have hj : (j : Int) = (n : Int) - x.1 0 := by
          simpa [j] using Int.toNat_of_nonneg hj0
        have hjLower : 1 ≤ j := by omega
        have hjUpper : j < 2 * n := by omega
        let k : Fin (2 * n - 1) := ⟨j - 1, by omega⟩
        let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
        have hx : x = fkIsingSquareBoundaryVertex n (.top, k1) := by
          apply Subtype.ext
          funext i
          fin_cases i <;>
            simp [k1, k, fkIsingSquareBoundaryVertex,
              fkIsingSquareBoundarySite, htop] <;> omega
        rw [hx]
        exact vertex_modifiedLaplacian_nonpos_of_topBoundary n hn k
      · apply vertex_modifiedLaplacian_nonpos_of_interior n hn x
        · simp [fkIsingSquareDirectionAvailable]
          omega
        · simp [fkIsingSquareDirectionAvailable]
          omega
        · simp [fkIsingSquareDirectionAvailable]
          omega
        · simp [fkIsingSquareDirectionAvailable]
          omega


theorem face_modifiedLaplacian_nonneg_of_interior
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n)
    (heast : c.1.1 + 1 < 2 * n)
    (hnorth : c.2.1 + 1 < 2 * n)
    (hwest : 0 < c.1.1) (hsouth : 0 < c.2.1) :
    0 <= isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c +
        isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c *
            (0 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c) := by
  have hmult : fkIsingSquareFullFaceGhostMultiplicity n c = 0 := by
    unfold fkIsingSquareFullFaceGhostMultiplicity
    split_ifs <;> omega
  simp [isingFermionicGhostRate, hmult]
  exact face_laplacian_nonneg_of_interior n hn c
    heast hnorth hwest hsouth


theorem face_modifiedLaplacian_nonneg_of_leftBoundary
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n)
    (hleft : c.1.1 = 0)
    (heast : c.1.1 + 1 < 2 * n)
    (hnorth : c.2.1 + 1 < 2 * n)
    (hsouth : 0 < c.2.1) :
    0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c +
        isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c *
            (0 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c) := by
  classical
  let cE := faceEastNeighbor n c heast
  let cN := faceNorthNeighbor n c hnorth
  let cS := faceSouthNeighbor n c hsouth
  let eN := faceNorthEdge n c
  let eE := faceEastEdge n c
  let eS := faceSouthEdge n c
  let eW := faceWestEdge n c
  let H := (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
  let F := fkIsingSquareBoundaryFullMedialObservable n hn
  have hSEeast : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .east := by
    change (fkIsingSquareInteriorCellKey n c).1 + 1 < (n : Int)
    simp [fkIsingSquareInteriorCellKey, hleft]
    omega
  have hSEnorth : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .north := by
    change (fkIsingSquareInteriorCellKey n c).2 < (n : Int)
    simp [fkIsingSquareInteriorCellKey] at hnorth ⊢
    omega
  have hSEwest : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .west := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).1 + 1
    simp [fkIsingSquareInteriorCellKey, hleft]
  have hSEsouth : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .south := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).2
    simp [fkIsingSquareInteriorCellKey] at hsouth ⊢
    omega
  have hNEeast : fkIsingSquareDirectionAvailable n (faceNEVertex n c) .east := by
    change (fkIsingSquareInteriorCellKey n c).1 + 1 < (n : Int)
    simp [fkIsingSquareInteriorCellKey, hleft]
    omega
  have hNEnorth : fkIsingSquareDirectionAvailable n (faceNEVertex n c) .north := by
    change (fkIsingSquareInteriorCellKey n c).2 + 1 < (n : Int)
    simp [fkIsingSquareInteriorCellKey] at hnorth ⊢
    omega
  have hNEwest : fkIsingSquareDirectionAvailable n (faceNEVertex n c) .west := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).1 + 1
    simp [fkIsingSquareInteriorCellKey, hleft]
  have hNEsouth : fkIsingSquareDirectionAvailable n (faceNEVertex n c) .south := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).2 + 1
    simp [fkIsingSquareInteriorCellKey]
  have heN : eN.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    rw [show eN = fkIsingSquareDirectionEdge n (faceNEVertex n c) .west
        hNEwest by
      dsimp [eN]
      exact faceNorthEdge_eq_west n c]
    exact fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
      (faceNEVertex n c) .west hNEwest hNEeast hNEnorth hNEwest hNEsouth
  have heE : eE.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    dsimp [eE, faceEastEdge]
    exact fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
      (faceSEVertex n c) .north hSEnorth hSEeast hSEnorth hSEwest hSEsouth
  have heS : eS.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    rw [show eS = fkIsingSquareDirectionEdge n (faceSEVertex n c) .west
        hSEwest by
      dsimp [eS]
      exact faceSouthEdge_eq_west n c]
    exact fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
      (faceSEVertex n c) .west hSEwest hSEeast hSEnorth hSEwest hSEsouth
  have hneighbors : (fkIsingSquareFullFaceGraph n).neighborFinset c =
      {cE, cN, cS} := by
    ext y
    rw [SimpleGraph.mem_neighborFinset]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨hcol, hup | hdown⟩ | ⟨hrow, hright | hwest⟩)
      · right; left
        apply Prod.ext
        · exact hcol.symm
        · apply Fin.ext
          simp [cN, faceNorthNeighbor]
          omega
      · right; right
        apply Prod.ext
        · exact hcol.symm
        · apply Fin.ext
          simp [cS, faceSouthNeighbor]
          omega
      · left
        apply Prod.ext
        · apply Fin.ext
          simp [cE, faceEastNeighbor]
          omega
        · exact hrow.symm
      · have hy := y.1.2
        omega
    · rintro (rfl | rfl | rfl)
      · exact Or.inr ⟨rfl, Or.inl (by simp [cE, faceEastNeighbor])⟩
      · exact Or.inl ⟨rfl, Or.inl (by simp [cN, faceNorthNeighbor])⟩
      · exact Or.inl ⟨rfl, Or.inr (by simp [cS, faceSouthNeighbor]; omega)⟩
  have hEN : cE ≠ cN := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.1.1) h
    simp [cE, cN, faceEastNeighbor, faceNorthNeighbor] at h0
  have hES : cE ≠ cS := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.1.1) h
    simp [cE, cS, faceEastNeighbor, faceSouthNeighbor] at h0
  have hNS : cN ≠ cS := by
    intro h
    have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.2.1) h
    simp [cN, cS, faceNorthNeighbor, faceSouthNeighbor] at h1
    omega
  have hLap : isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) H c =
      (H cE - H c) + (H cN - H c) + (H cS - H c) := by
    unfold isingFiniteGraphLaplacian
    rw [hneighbors]
    simp [hEN, hES, hNS]
    ring
  have hdN := face_difference_north n hn c hnorth
  have hdE := face_difference_east n hn c heast
  have hdS := face_difference_south n hn c hsouth
  change H cN - H c = _ at hdN
  change H cE - H c = _ at hdE
  change H cS - H c = _ at hdS
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .horizontal := by
    dsimp [eN, faceNorthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisE : (fkIsingSquareOrientedEdge n eE).axis = .vertical := by
    dsimp [eE, faceEastEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .horizontal := by
    dsimp [eS, faceSouthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .vertical := by
    dsimp [eW, faceWestEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eN haxisN with
    ⟨_, hNEt, hNSt, hNNt⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eE haxisE with
    ⟨hEWt, _, hESt, hENt⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eS haxisS with
    ⟨hSWt, _, hSSt, hSNt⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eW haxisW with
    ⟨_, hWEt, hWSt, _⟩
  have hprojNE : isingProj (-1) (F eN) = isingProj (-1) (F eE) := by
    calc
      isingProj (-1) (F eN) =
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eN, .east)) := by
        rw [← hNEt]
        simpa [F] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eN heN .east
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eE, .north)) := faceNorthEast_observable_eq n hn c
      _ = isingProj (-1) (F eE) := by
        rw [← hENt]
        symm
        simpa [F] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eE heE .north
  have hprojES : isingProj (-Complex.I) (F eE) =
      isingProj (-Complex.I) (F eS) := by
    calc
      isingProj (-Complex.I) (F eE) =
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eE, .west)) := by
        rw [← hEWt]
        simpa [F] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eE heE .west
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eS, .north)) := faceEastSouth_observable_eq n hn c
      _ = isingProj (-Complex.I) (F eS) := by
        rw [← hSNt]
        symm
        simpa [F] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eS heS .north
  have heWleft : eW = fkIsingSquareLeftVerticalEdge n hn c.2 := by
    apply Subtype.ext
    change s(faceSWVertex n c,
        fkIsingSquareNeighbor n (faceSWVertex n c) .north _) =
      s(fkIsingSquareLeftVerticalUpper n hn c.2,
        fkIsingSquareNeighbor n
          (fkIsingSquareLeftVerticalUpper n hn c.2) .south _)
    rw [Sym2.eq_iff]
    apply Or.inr
    constructor <;>
      apply Subtype.ext <;>
      funext i <;>
      fin_cases i <;>
      simp [faceSWVertex, fkIsingSquareInteriorCellKey,
        fkIsingSquareLeftVerticalLower, fkIsingSquareLeftVerticalUpper,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, hleft]
  have hphase : isingProj 1 (F eS) =
      isingLambda * isingProj Complex.I (F eN) := by
    calc
      isingProj 1 (F eS) =
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eS, .west)) := by
        rw [← hSWt]
        simpa [F] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eS heS .west
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eW, .south)) := faceSouthWest_observable_eq n hn c
      _ = isingLambda *
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eW, .east)) := by
        rw [heWleft]
        exact left_boundary_endpoint_observable_phase n hn c.2
      _ = isingLambda *
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eN, .south)) := by
        rw [faceWestNorth_observable_eq n hn c]
      _ = isingLambda * isingProj Complex.I (F eN) := by
        rw [← hNSt]
        congr 1
        symm
        simpa [F] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eN heN .south
  have hdiv : isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) H c =
      isingPrimalProjectionDivergenceWithoutWest (F eN) (F eE) (F eS) := by
    rw [hLap, hdE, hdN, hdS]
    rw [fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eE heE .south,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eE heE .west,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eN heN .north,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eN heN .east,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eS heS .south,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eS heS .west]
    unfold isingPrimalProjectionDivergenceWithoutWest
    rw [hNEt, hNNt, hEWt, hESt, hSSt, hSWt]
    ring
  let r : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (faceWestEastDart n c)
  have hrface : fkIsingSquareFullFaceOfRadialIncidence n hn r = c := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [r, faceWestEastDart, eW, faceWestEdge, faceSWVertex,
      fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  have hrwired : fkIsingSquareFullVertexFixedBoundary n
      (fkIsingSquareInteriorRadialEndpoint n hn r) := by
    change fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n (eW, .east))
    simp [fkIsingSquareWiredArc, eW, faceWestEdge, faceSWVertex,
      fkIsingSquareInteriorCellKey, fkIsingSquareDartEndpoint,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite, hleft]
  have hgap := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex
    n hn r
  rw [hrface, vertex_fixedBoundary_eq_zero n hn _ hrwired, sub_zero] at hgap
  have hH : H c = Complex.normSq (isingProj Complex.I (F eN)) := by
    calc
      H c = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .east)) :=
        hgap
      _ = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .south)) := by
        unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
        rw [faceWestNorth_observable_eq n hn c]
      _ = Complex.normSq (isingProj Complex.I (F eN)) := by
        rw [fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eN heN .south, hNSt]
  have hmult : fkIsingSquareFullFaceGhostMultiplicity n c = 1 := by
    simp [fkIsingSquareFullFaceGhostMultiplicity, hleft]
  change 0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) H c +
    isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n) c *
      (0 - H c)
  rw [hdiv, isingFermionicGhostRate, hmult, hH]
  simpa [sub_eq_add_neg] using
    isingPrimalProjectionDivergenceWithoutWest_left_add_ghost_nonneg
      (F eN) (F eE) (F eS) hprojNE hprojES hphase


theorem face_modifiedLaplacian_nonneg_of_not_fixedBoundary
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n)
    (hcFree : ¬ fkIsingSquareFullFaceFixedBoundary n c) :
    0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c +
        isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c *
            (0 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c) := by
  have hsouth : 0 < c.2.1 := by
    by_contra h
    apply hcFree
    left
    omega
  have heast : c.1.1 + 1 < 2 * n := by
    have hcBound := c.1.isLt
    by_contra h
    apply hcFree
    right
    left
    omega
  have hnorth : c.2.1 + 1 < 2 * n := by
    have hcBound := c.2.isLt
    by_contra h
    apply hcFree
    right
    right
    omega
  by_cases hleft : c.1.1 = 0
  · exact face_modifiedLaplacian_nonneg_of_leftBoundary
      n hn c hleft heast hnorth hsouth
  · exact face_modifiedLaplacian_nonneg_of_interior
      n hn c heast hnorth (by omega) hsouth


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
