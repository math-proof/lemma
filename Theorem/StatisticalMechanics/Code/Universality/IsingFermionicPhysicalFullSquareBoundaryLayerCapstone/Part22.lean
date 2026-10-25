/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part21


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem bottomRightCornerCycleCarrier_of_adj
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hx : bottomRightCornerCycleCarrier n hn x)
    (hxy : (fkIsingSquareWiredLoopGraph n hn
      (fkIsingSquareClosePerimeter n omega)).Adj x y) :
    bottomRightCornerCycleCarrier n hn y := by
  have hother := cornerDart_ne_source_terminal_of_not_boundary n hn
    (bottomRightCornerOtherDart n hn)
    (bottomRightCornerOtherDart_not_boundary n hn)
  have hcross := cornerDart_ne_source_terminal_of_not_boundary n hn
    (bottomRightCornerCrossDart n hn)
    (bottomRightCornerCrossDart_not_boundary n hn)
  have hcrossMate := cornerDart_ne_source_terminal_of_not_boundary n hn
    (fkIsingSquarePerimeterEdge n .right
      (bottomRightCornerZero n hn), .south)
    (bottomRightCornerCrossMate_not_boundary n hn)
  have hotherMate := cornerDart_ne_source_terminal_of_not_boundary n hn
    (fkIsingSquarePerimeterEdge n .right
      (bottomRightCornerZero n hn), .west)
    (bottomRightCornerOtherMate_not_boundary n hn)
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hxy with ⟨-, -, rfl⟩ | rfl <;>
    simp [bottomRightCornerCycleCarrier,
      fkIsingSquareWiredIncidenceMate, fkIsingSquareWiredTransitionMate,
      bottomRightCornerOtherDart_localMate,
      bottomRightCornerCrossDart_localMate,
      bottomRightCornerCrossMate_localMate,
      bottomRightCornerOtherMate_localMate,
      bottomRightCornerCrossDart_bondMate,
      bottomRightCornerCrossMate_bondMate,
      bottomRightCornerOtherDart_bondMate,
      bottomRightCornerOtherMate_bondMate,
      hother.1, hother.2, hcross.1, hcross.2,
      hcrossMate.1, hcrossMate.2, hotherMate.1, hotherMate.2]

theorem bottomRightCornerCycleCarrier_not_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {z : FKIsingSquareWiredCarrier n}
    (hz : bottomRightCornerCycleCarrier n hn z) :
    ¬ (fkIsingSquareWiredLoopGraph n hn
      (fkIsingSquareClosePerimeter n omega)).Reachable .source z := by
  intro hreach
  obtain ⟨p⟩ := hreach.symm
  have htransport : ∀ {a b : FKIsingSquareWiredCarrier n},
      (fkIsingSquareWiredLoopGraph n hn
        (fkIsingSquareClosePerimeter n omega)).Walk a b →
      bottomRightCornerCycleCarrier n hn a →
      bottomRightCornerCycleCarrier n hn b := by
    intro a b q
    induction q with
    | nil => exact fun ha => ha
    | cons hadj q ih =>
        intro ha
        exact ih (bottomRightCornerCycleCarrier_of_adj n hn omega ha hadj)
  have hsource := htransport p hz
  simpa [bottomRightCornerCycleCarrier] using hsource

theorem bottomRightCornerOtherMate_not_mem_exploration
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace
      (Sym2 (fkIsingSquareBoundaryDeletedPlanar n).V)) :
    (.dart (fkIsingSquarePerimeterEdge n .right
      (bottomRightCornerZero n hn), .west) : FKIsingSquareWiredCarrier n) ∉
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration omega := by
  change (.dart (fkIsingSquarePerimeterEdge n .right
      (bottomRightCornerZero n hn), .west) : FKIsingSquareWiredCarrier n) ∉
    fkIsingSquareWiredExplorationOrder n hn
      (fkIsingSquareClosePerimeter n omega)
  rw [mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
  apply bottomRightCornerCycleCarrier_not_reachable n hn omega
  simp [bottomRightCornerCycleCarrier]


theorem bottomRightCorner_inward_observable_eq_zero
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .west)) = 0 := by
  unfold FKIsingDobrushinDomain.fermionicObservable
  apply Finset.sum_eq_zero
  intro omega _
  unfold FKIsingDobrushinDomain.fermionicSummand
  rw [if_neg (bottomRightCornerOtherMate_not_mem_exploration n hn omega)]


theorem bottomRightCorner_inward_increment_eq_zero
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .west)) = 0 := by
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [bottomRightCorner_inward_observable_eq_zero n hn]
  exact Complex.normSq_zero

theorem bottomRightCornerCrossDart_bondTurn
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondTurn n hn (bottomRightCornerCrossDart n hn)
      (fkIsingSquareWiredBondMate n hn (bottomRightCornerCrossDart n hn)) = 4 := by
  let d := bottomRightCornerCrossDart n hn
  have hmate : fkIsingSquareWiredBondMate n hn d =
      (fkIsingSquarePerimeterEdge n .right (bottomRightCornerZero n hn),
        .south) := by
    simpa [d] using bottomRightCornerCrossDart_bondMate n hn
  have hfwd : ¬ fkIsingSquareWiredBoundaryForward n hn d
      (fkIsingSquareWiredBondMate n hn d) := by
    intro h
    rcases h with ⟨hd, -⟩ | ⟨j, hd, -⟩
    · exact bottomRightCornerCrossDart_ne_source n hn hd
    · exact bottomRightCornerCrossDart_not_boundary n hn
        ⟨.west j, hd.symm⟩
  have hrev : ¬ fkIsingSquareWiredBoundaryReverse n hn d
      (fkIsingSquareWiredBondMate n hn d) := by
    rw [fkIsingSquareWiredBoundaryReverse, hmate]
    intro h
    rcases h with ⟨hd, -⟩ | ⟨j, hd, -⟩
    · have hend := congrArg (fkIsingSquareDartEndpoint n) hd
      have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) hend
      simp [bottomRightCornerZero, fkIsingSquareWiredSourceDart,
        fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
        fkIsingSquareDartEndpoint, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareCornerSide, fkIsingSquareEndpointForDirection,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareMarkedA, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] at h0
      omega
    · exact bottomRightCornerCrossMate_not_boundary n hn
        ⟨.west j, hd.symm⟩
  rw [fkIsingSquareWiredBondTurn, if_neg hfwd, if_neg hrev, hmate]
  simp [fkIsingSquareOrientedPrincipalBondTurn,
    fkIsingSquareSignedEighthTurn, fkIsingSquareWiredCarrierTangentCode,
    fkIsingSquareCornerTangentCode, FKIsingSquareDirection.eighthTurn,
    d, bottomRightCornerCrossDart, bottomRightCornerLast,
    bottomRightCornerZero, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
    fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation]

theorem bottomRightCornerCrossDart_bondPhase
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondPhase n hn (bottomRightCornerCrossDart n hn) =
      Complex.I := by
  unfold fkIsingSquareWiredBondPhase
  rw [bottomRightCornerCrossDart_bondTurn]
  convert exp_pi_div_two_mul_I using 1 <;> push_cast <;> ring


theorem bottomRightCorner_inward_increment_eq
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .bottom
          (bottomRightCornerLast n hn), .north)) =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .right
          (bottomRightCornerZero n hn), .west)) := by
  let d := bottomRightCornerCrossDart n hn
  have hbond := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate n hn d
    (bottomRightCornerCrossDart_ne_source n hn)
    (bottomRightCornerCrossDart_ne_terminal n hn)
  rw [bottomRightCornerCrossDart_bondMate n hn] at hbond
  have hbottom :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .bottom (bottomRightCornerLast n hn)
  have hright := fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    n hn .right (bottomRightCornerZero n hn)
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom
        (bottomRightCornerLast n hn), .east)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom
        (bottomRightCornerLast n hn), .north)) at hbottom
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .west)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .south)) at hright
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .south)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom
        (bottomRightCornerLast n hn), .east)) at hbond
  exact hbottom.symm.trans (hbond.symm.trans hright.symm)


theorem bottomRightCorner_vertex_difference_west
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    let zero := bottomRightCornerZero n hn
    let x0 := fkIsingSquareBoundaryVertex n (.bottom, last)
    let x1 := fkIsingSquareBoundaryVertex n (.right, zero)
    let e := fkIsingSquarePerimeterEdge n .bottom last
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x0 -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x1 =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) := by
  let last := bottomRightCornerLast n hn
  let zero := bottomRightCornerZero n hn
  let x0 := fkIsingSquareBoundaryVertex n (.bottom, last)
  let x1 := fkIsingSquareBoundaryVertex n (.right, zero)
  let ep := fkIsingSquarePerimeterEdge n .bottom last
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
  linarith


theorem bottomRightCorner_vertex_laplacian_eq_increment_divergence
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    let zero := bottomRightCornerZero n hn
    let x := fkIsingSquareBoundaryVertex n (.right, zero)
    let eN := fkIsingSquarePerimeterEdge n .right zero
    let eW := fkIsingSquarePerimeterEdge n .bottom last
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .west)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .north))) +
        (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .north)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .west))) := by
  let last := bottomRightCornerLast n hn
  let zero := bottomRightCornerZero n hn
  let x := fkIsingSquareBoundaryVertex n (.right, zero)
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, zero, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, zero, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let xN := fkIsingSquareNeighbor n x .north hnorth
  let xW := fkIsingSquareNeighbor n x .west hwest
  let eN := fkIsingSquarePerimeterEdge n .right zero
  let eW := fkIsingSquarePerimeterEdge n .bottom last
  let H := (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
  have hneighbors : (fkSquareBoxPlanar n).G.neighborFinset x = {xN, xW} := by
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
      · have hi := congrFun h 1
        simp [Pi.add_apply, x, zero, bottomRightCornerZero,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hi
        have hy := fkIsingSquareVertex_coordinate_bounds n y 1
        omega
      · left
        apply Subtype.ext
        funext i
        fin_cases i
        · have hi := congrFun h 0
          simp [Pi.add_apply] at hi
          simpa [xN, fkIsingSquareNeighbor,
            fkIsingSquareNeighborSite] using hi.symm
        · have hi := congrFun h 1
          simp [Pi.add_apply] at hi
          change y.1 1 = x.1 1 + 1
          omega
    · rintro (rfl | rfl)
      · exact fkIsingSquare_adj_neighbor n x .north hnorth
      · exact fkIsingSquare_adj_neighbor n x .west hwest
  have hNW : xN ≠ xW := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) h
    simp [xN, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hLap : isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x =
      (H xN - H x) + (H xW - H x) := by
    unfold isingFiniteGraphLaplacian
    rw [hneighbors]
    simp [hNW]
    ring
  have hdN := vertex_difference_north n hn x hnorth hwest
  have hdW := bottomRightCorner_vertex_difference_west n hn
  change H xN - H x = _ at hdN
  have hx0 : fkIsingSquareBoundaryVertex n (.bottom, last) = xW := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [xW, x, last, zero, bottomRightCornerLast,
        bottomRightCornerZero, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite] <;> omega
  change H (fkIsingSquareBoundaryVertex n (.bottom, last)) - H x = _ at hdW
  rw [hx0] at hdW
  have heN : fullVertexNorthEdge n x hnorth = eN := by rfl
  rw [heN] at hdN
  rw [show fkIsingSquarePerimeterEdge n .bottom last = eW by rfl] at hdW
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x = _
  rw [hLap, hdN, hdW]


theorem bottomRightCorner_vertex_laplacian_eq_corner_divergence
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    let zero := bottomRightCornerZero n hn
    let x := fkIsingSquareBoundaryVertex n (.right, zero)
    let a := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom last, .west))
    let b := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right zero, .west))
    let d := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right zero, .north))
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      (b - d) + (b - a) := by
  dsimp only
  rw [bottomRightCorner_vertex_laplacian_eq_increment_divergence n hn]
  rw [bottomRightCorner_inward_increment_eq n hn]


theorem vertex_modifiedLaplacian_nonpos_of_bottomRightCorner_of_increment_bound
    (n : Nat) (hn : 0 < n)
    (hcorner :
      let last := bottomRightCornerLast n hn
      let zero := bottomRightCornerZero n hn
      let a := fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .bottom last, .west))
      let b := fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .right zero, .west))
      let d := fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .right zero, .north))
      2 * (1 + isingFermionicGhostCoefficient) * b ≤ a + d) :
    let zero := bottomRightCornerZero n hn
    let x := fkIsingSquareBoundaryVertex n (.right, zero)
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
      ≤ 0 := by
  let last := bottomRightCornerLast n hn
  let zero := bottomRightCornerZero n hn
  let x := fkIsingSquareBoundaryVertex n (.right, zero)
  let a := fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .bottom last, .west))
  let b := fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .right zero, .west))
  let d := fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .right zero, .north))
  have hlap := bottomRightCorner_vertex_laplacian_eq_corner_divergence n hn
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
        (b - d) + (b - a) at hlap
  have hgap := boundaryLayer_inwardIncrement_eq_one_sub_vertex
    n hn .right zero (by decide)
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
  change (b - d) + (b - a) +
    (isingFermionicGhostCoefficient * 2) * b ≤ 0
  have hc : 2 * (1 + isingFermionicGhostCoefficient) * b ≤ a + d := hcorner
  nlinarith


theorem bottomRightCorner_increment_bound
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    let zero := bottomRightCornerZero n hn
    let a := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom last, .west))
    let b := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right zero, .west))
    let d := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right zero, .north))
    2 * (1 + isingFermionicGhostCoefficient) * b ≤ a + d := by
  dsimp only
  rw [bottomRightCorner_inward_increment_eq_zero n hn]
  have ha := isingPrimitiveIncrement_nonneg
    ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquarePerimeterEdge n .bottom
        (bottomRightCornerLast n hn), .west)))
  have hd := isingPrimitiveIncrement_nonneg
    ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .north)))
  change 0 ≤ fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .bottom
      (bottomRightCornerLast n hn), .west)) at ha
  change 0 ≤ fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .right
      (bottomRightCornerZero n hn), .north)) at hd
  nlinarith


theorem vertex_modifiedLaplacian_nonpos_of_bottomRightCorner
    (n : Nat) (hn : 0 < n) :
    let zero := bottomRightCornerZero n hn
    let x := fkIsingSquareBoundaryVertex n (.right, zero)
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
      ≤ 0 := by
  apply vertex_modifiedLaplacian_nonpos_of_bottomRightCorner_of_increment_bound
  exact bottomRightCorner_increment_bound n hn


theorem bottomRightCorner_rightComplement_phase
    (n : Nat) (hn : 0 < n) :
    let k0 := bottomRightCornerZero n hn
    isingProj (-Complex.I)
        (fkIsingSquareBoundaryLayerComplementVertexFermion n hn .right k0) =
      -isingLambda * isingProj 1
        (fkIsingSquareBoundaryLayerComplementVertexFermion n hn .right k0) := by
  let k0 := bottomRightCornerZero n hn
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .right k0
  let F := D.fermionicObservable (.dart (e, .east))
  have hline : (starRingEnd Complex) F = Complex.I * F := by
    have h := fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment
      n hn (.dart (e, .east))
    have ht : fkIsingSquareWiredDirectedTangent n hn (.dart (e, .east)) =
        Complex.I := by
      simpa only [e] using
        fkIsingSquareBoundaryLayerComplementInward_directedTangent
          n hn .right k0
    rw [ht] at h
    exact conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq Complex.I F
      (by simpa only [D, F, fkIsingSquareBoundaryPrimitiveIncrement,
        isingPrimitiveIncrement] using h)
  have hvertex :
      fkIsingSquareBoundaryLayerComplementVertexFermion n hn .right k0 =
        (isingFermionicBoundaryVertexNormalization : Complex) *
          (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerComplementVertexFermion
    change (isingFermionicBoundaryVertexNormalization : Complex) *
      (F + D.fermionicObservable (.dart (e, .north))) = _
    have hep :=
      fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint
        n hn .right k0
    change D.fermionicObservable (.dart (e, .north)) = F * isingLambda⁻¹ at hep
    rw [hep]
    change _ * (F + F * isingLambda⁻¹) = _
    ring
  change isingProj (-Complex.I)
      (fkIsingSquareBoundaryLayerComplementVertexFermion n hn .right k0) = _
  rw [hvertex, isingLambda_inv_val, isingLambda_val]
  have hre := congrArg Complex.re hline
  have him := congrArg Complex.im hline
  simp at hre him
  have hy : F.im = -F.re := by linarith [hre]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)
  apply Complex.ext <;>
    simp [isingProj, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im] <;>
    rw [hy] <;> ring_nf <;> nlinarith [hsqrt]


theorem bottomRightCorner_bottomStandard_phase
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    isingProj (-1)
        (fkIsingSquareBoundaryLayerVertexFermion n hn .bottom last) =
      -isingLambda * isingProj (-Complex.I)
        (fkIsingSquareBoundaryLayerVertexFermion n hn .bottom last) := by
  let last := bottomRightCornerLast n hn
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .bottom last
  let F := D.fermionicObservable (.dart (e, .west))
  have hline : (starRingEnd Complex) F = F := by
    have h := fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment
      n hn (.dart (e, .west))
    have ht : fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west)) = 1 := by
      simpa only [e] using fkIsingSquareBoundaryLayerInward_directedTangent
        n hn .bottom last
    rw [ht, one_mul] at h
    simpa only [one_mul] using
      (conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq 1 F
        (by simpa only [D, F, fkIsingSquareBoundaryPrimitiveIncrement,
          isingPrimitiveIncrement, one_mul] using h))
  have hvertex : fkIsingSquareBoundaryLayerVertexFermion n hn .bottom last =
      (isingFermionicBoundaryVertexNormalization : Complex) *
        (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerVertexFermion
    change (isingFermionicBoundaryVertexNormalization : Complex) *
      (F + D.fermionicObservable (.dart (e, .south))) = _
    have hep := fkIsingSquareBoundaryLayer_fermionicObservable_endpoint
      n hn .bottom last
    change D.fermionicObservable (.dart (e, .south)) = F * isingLambda⁻¹ at hep
    rw [hep]
    change _ * (F + F * isingLambda⁻¹) = _
    ring
  change isingProj (-1)
      (fkIsingSquareBoundaryLayerVertexFermion n hn .bottom last) = _
  rw [hvertex, isingLambda_inv_val, isingLambda_val]
  have hre := congrArg Complex.re hline
  have him := congrArg Complex.im hline
  simp at hre him
  have hy : F.im = 0 := by linarith [him]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)
  apply Complex.ext <;>
    simp [isingProj, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im] <;>
    rw [hy] <;> ring_nf <;> nlinarith [hsqrt]


theorem topRightCorner_rightStandard_phase
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    isingProj Complex.I
        (fkIsingSquareBoundaryLayerVertexFermion n hn .right last) =
      -isingLambda * isingProj (-1)
        (fkIsingSquareBoundaryLayerVertexFermion n hn .right last) := by
  let last := bottomRightCornerLast n hn
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .right last
  let F := D.fermionicObservable (.dart (e, .west))
  have hline : (starRingEnd Complex) F = -Complex.I * F := by
    have h := fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment
      n hn (.dart (e, .west))
    have ht : fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west)) =
        -Complex.I := by
      simpa only [e] using fkIsingSquareBoundaryLayerInward_directedTangent
        n hn .right last
    rw [ht] at h
    exact conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq (-Complex.I) F
      (by simpa only [D, F, fkIsingSquareBoundaryPrimitiveIncrement,
        isingPrimitiveIncrement] using h)
  have hvertex : fkIsingSquareBoundaryLayerVertexFermion n hn .right last =
      (isingFermionicBoundaryVertexNormalization : Complex) *
        (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerVertexFermion
    change (isingFermionicBoundaryVertexNormalization : Complex) *
      (F + D.fermionicObservable (.dart (e, .south))) = _
    have hep := fkIsingSquareBoundaryLayer_fermionicObservable_endpoint
      n hn .right last
    change D.fermionicObservable (.dart (e, .south)) = F * isingLambda⁻¹ at hep
    rw [hep]
    ring
  change isingProj Complex.I
      (fkIsingSquareBoundaryLayerVertexFermion n hn .right last) = _
  rw [hvertex, isingLambda_inv_val, isingLambda_val]
  have hre := congrArg Complex.re hline
  have him := congrArg Complex.im hline
  simp at hre him
  have hy : F.im = F.re := by linarith [hre]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)
  apply Complex.ext <;>
    simp [isingProj, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im] <;>
    rw [hy] <;> ring_nf <;> nlinarith [hsqrt]


theorem topRightCorner_topComplement_phase
    (n : Nat) (hn : 0 < n) :
    let k0 := bottomRightCornerZero n hn
    isingProj (-1)
        (fkIsingSquareBoundaryLayerComplementVertexFermion n hn .top k0) =
      -isingLambda * isingProj (-Complex.I)
        (fkIsingSquareBoundaryLayerComplementVertexFermion n hn .top k0) := by
  let k0 := bottomRightCornerZero n hn
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .top k0
  let F := D.fermionicObservable (.dart (e, .west))
  have hline : (starRingEnd Complex) F = F := by
    have h := fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment
      n hn (.dart (e, .west))
    have ht : fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west)) = 1 := by
      simpa only [e] using
        fkIsingSquareBoundaryLayerComplementInward_directedTangent
          n hn .top k0
    rw [ht, one_mul] at h
    simpa only [one_mul] using
      (conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq 1 F
        (by simpa only [D, F, fkIsingSquareBoundaryPrimitiveIncrement,
          isingPrimitiveIncrement, one_mul] using h))
  have hvertex :
      fkIsingSquareBoundaryLayerComplementVertexFermion n hn .top k0 =
        (isingFermionicBoundaryVertexNormalization : Complex) *
          (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerComplementVertexFermion
    change (isingFermionicBoundaryVertexNormalization : Complex) *
      (F + D.fermionicObservable (.dart (e, .south))) = _
    have hep :=
      fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint
        n hn .top k0
    change D.fermionicObservable (.dart (e, .south)) = F * isingLambda⁻¹ at hep
    rw [hep]
    ring
  change isingProj (-1)
      (fkIsingSquareBoundaryLayerComplementVertexFermion n hn .top k0) = _
  rw [hvertex, isingLambda_inv_val, isingLambda_val]
  have hre := congrArg Complex.re hline
  have him := congrArg Complex.im hline
  simp at hre him
  have hy : F.im = 0 := by linarith [him]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)
  apply Complex.ext <;>
    simp [isingProj, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im] <;>
    rw [hy] <;> ring_nf <;> nlinarith [hsqrt]

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
