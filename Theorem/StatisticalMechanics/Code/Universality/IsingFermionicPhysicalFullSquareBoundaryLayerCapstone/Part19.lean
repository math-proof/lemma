/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part18


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem top_boundary_projection_cycle
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.top, k1)
    let hsouth : fkIsingSquareDirectionAvailable n x .south := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    let east := fkIsingSquareTopBoundaryMedialObservable n hn k0
    let south := fkIsingSquareBoundaryFullMedialObservable n hn
      (fullVertexSouthEdge n x hsouth)
    let west := fkIsingSquareTopBoundaryMedialObservable n hn k1
    isingProj Complex.I east = isingProj Complex.I south ∧
      isingProj (-1) south = isingProj (-1) west := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.top, k1)
  let heast : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let eE := fullVertexEastEdge n x heast
  let eS := fullVertexSouthEdge n x hsouth
  let eW := fullVertexWestEdge n x hwest
  have heE : fkIsingSquarePerimeterEdge n .top k0 = eE := by
    apply Subtype.ext
    simp only [eE, fullVertexEastEdge, fkIsingSquarePerimeterEdge,
      fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;>
      apply Subtype.ext <;> funext i <;> fin_cases i <;>
      simp [x, fkIsingSquarePerimeterDirection,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  have heW : fkIsingSquarePerimeterEdge n .top k1 = eW := rfl
  have heS : eS.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [topBoundarySouthInteriorRadialCell, eS, x, k1] using
      fkIsingSquareInteriorRadialCell_not_mem_perimeter n
        (topBoundarySouthInteriorRadialCell n hn k)
  have haxisE : (fkIsingSquareOrientedEdge n eE).axis = .horizontal := by
    dsimp [eE, fullVertexEastEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .vertical := by
    dsimp [eS, fullVertexSouthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .horizontal := by
    dsimp [eW, fullVertexWestEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eS haxisS with
    ⟨_, hSE, _, hSN⟩
  have hESobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .south)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .east)) := by
    let d : FKIsingSquareInteriorRadialDart n := ⟨(eS, .east),
      (topBoundarySouthInteriorRadialCell n hn k).2 .east⟩
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eE, .south) := by
      rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _ d.2]
      change fkIsingSquareBondMate n hn
        (fkIsingSquareDirectionDart n x .south hsouth .counterclockwise) = _
      simp only [fkIsingSquareBondMate,
        fkIsingSquareDirectionDart_endpoint,
        fkIsingSquareDirectionDart_direction,
        fkIsingSquareDirectionDart_turn]
      have hdir : fkIsingSquareNextDirection n x .south = .east := by
        simp [fkIsingSquareNextDirection, heast]
      calc
        _ = fkIsingSquareDirectionDart n x .east heast .clockwise :=
          fkIsingSquareDirectionDart_congr n x hdir _ _ _
        _ = (eE, .south) := by
          rw [← heE]
          apply fkIsingSquareDart_key_injective n
          simp [fkIsingSquareDirectionDart, fkIsingSquareDartEndpoint,
            fkIsingSquareDartDirection, fkIsingSquareSideCorner,
            fkIsingSquareCornerSide, fkIsingSquareEndpointForDirection,
            fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
            fkIsingSquareOrientedEdge_directionEdge,
            fkIsingSquareDirectionEdgeOrientation, x,
            fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
            fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcE := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eE haxisE
      have hcS := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eS haxisS
      change fkIsingSquareWiredDirectedTangentCode n hn (.bond (eE, .south)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond (eS, .east)) [ZMOD 8]
      rw [hcE.2.2.1, hcS.2.1]
    have h := fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
      n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) = _ at h
    rw [hmate] at h
    simpa [d] using h
  have hSWobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := by
    let d : FKIsingSquareInteriorRadialDart n := ⟨(eS, .north),
      (topBoundarySouthInteriorRadialCell n hn k).2 .north⟩
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eW, .east) := by
      rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _ d.2]
      change fkIsingSquareBondMate n hn
        (fkIsingSquareDirectionDart n x .south hsouth .clockwise) = _
      simp only [fkIsingSquareBondMate,
        fkIsingSquareDirectionDart_endpoint,
        fkIsingSquareDirectionDart_direction,
        fkIsingSquareDirectionDart_turn]
      have hdir : fkIsingSquarePreviousDirection n x .south = .west := by
        simp [fkIsingSquarePreviousDirection, hwest]
      calc
        _ = fkIsingSquareDirectionDart n x .west hwest .counterclockwise :=
          fkIsingSquareDirectionDart_congr n x hdir _ _ _
        _ = (eW, .east) := rfl
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcW := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eW haxisW
      have hcS := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eS haxisS
      change fkIsingSquareWiredDirectedTangentCode n hn (.bond (eW, .east)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond (eS, .north)) [ZMOD 8]
      rw [hcW.2.1, hcS.2.2.2]
      decide
    have h := fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
      n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) = _ at h
    rw [hmate] at h
    simpa [d] using h.symm
  let east := fkIsingSquareTopBoundaryMedialObservable n hn k0
  let south := fkIsingSquareBoundaryFullMedialObservable n hn eS
  let west := fkIsingSquareTopBoundaryMedialObservable n hn k1
  constructor
  · calc
      isingProj Complex.I east =
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eE, .south)) := by
        rw [← heE]
        simpa [east] using
          fkIsingSquareTopBoundaryMedialObservable_projection_south n hn k0
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .east)) := hESobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .east)))
          south := by
        symm
        simpa [south] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eS heS .east
      _ = isingProj Complex.I south := by rw [hSE]
  · calc
      isingProj (-1) south = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .north)))
          south := by rw [hSN]
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) := by
        simpa [south] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eS heS .north
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := hSWobs
      _ = isingProj (-1) west := by
        rw [← heW]
        simpa [west] using
          (fkIsingSquareTopBoundaryMedialObservable_projection_east
            n hn k1).symm


theorem top_boundary_vertex_laplacian_eq_increment_divergence
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.top, k1)
    let heast : fkIsingSquareDirectionAvailable n x .east := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    let hsouth : fkIsingSquareDirectionAvailable n x .south := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    let hwest : fkIsingSquareDirectionAvailable n x .west := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
      omega
    let eE := fullVertexEastEdge n x heast
    let eS := fullVertexSouthEdge n x hsouth
    let eW := fullVertexWestEdge n x hwest
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .west)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .north))) +
        (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .east)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .south))) +
        (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .east)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .south))) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.top, k1)
  let heast : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let xE := fkIsingSquareNeighbor n x .east heast
  let xS := fkIsingSquareNeighbor n x .south hsouth
  let xW := fkIsingSquareNeighbor n x .west hwest
  let eE := fullVertexEastEdge n x heast
  let eS := fullVertexSouthEdge n x hsouth
  let eW := fullVertexWestEdge n x hwest
  let H := (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
  have hneighbors : (fkSquareBoxPlanar n).G.neighborFinset x =
      {xE, xS, xW} := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hxy
      change (hypercubicLattice 2).Adj x.1 y.1 at hxy
      rcases adj_neighbor_cases x.1 y.1 hxy with h | h | h | h
      · right; right
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
      · left
        apply Subtype.ext
        funext i
        fin_cases i
        · have hi := congrFun h 0
          simp [Pi.add_apply] at hi
          change y.1 0 = x.1 0 + 1
          omega
        · have hi := congrFun h 1
          simp [Pi.add_apply] at hi
          simpa [xE, fkIsingSquareNeighbor,
            fkIsingSquareNeighborSite] using hi.symm
      · right; left
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
        simp [Pi.add_apply, x, fkIsingSquareBoundaryVertex,
          fkIsingSquareBoundarySite] at hi
        have hy := fkIsingSquareVertex_coordinate_bounds n y 1
        omega
    · rintro (rfl | rfl | rfl)
      · exact fkIsingSquare_adj_neighbor n x .east heast
      · exact fkIsingSquare_adj_neighbor n x .south hsouth
      · exact fkIsingSquare_adj_neighbor n x .west hwest
  have hES : xE ≠ xS := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) h
    simp [xE, xS, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hEW : xE ≠ xW := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) h
    simp [xE, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hSW : xS ≠ xW := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) h
    simp [xS, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hLap : isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x =
      (H xE - H x) + (H xS - H x) + (H xW - H x) := by
    unfold isingFiniteGraphLaplacian
    rw [hneighbors]
    simp [hES, hEW, hSW]
    ring
  have hdE := top_boundary_vertex_difference_east n hn k
  have hdS := vertex_difference_south n hn x hsouth heast
  have hdW := vertex_difference_west n hn x hwest hsouth
  change H xS - H x = _ at hdS
  change H xW - H x = _ at hdW
  have hx0 : fkIsingSquareBoundaryVertex n (.top, k0) = xE := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [xE, x, fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k0, k1] <;> ring
  have heE : fkIsingSquarePerimeterEdge n .top k0 = eE := by
    apply Subtype.ext
    simp only [eE, fullVertexEastEdge, fkIsingSquarePerimeterEdge,
      fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;>
      apply Subtype.ext <;> funext i <;> fin_cases i <;>
      simp [x, fkIsingSquarePerimeterDirection,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  change H (fkIsingSquareBoundaryVertex n (.top, k0)) - H x = _ at hdE
  rw [hx0, heE] at hdE
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x = _
  rw [hLap, hdE, hdS, hdW]


theorem top_boundary_vertex_laplacian_eq_projectionDivergenceWithoutNorth
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.top, k1)
    let hsouth : fkIsingSquareDirectionAvailable n x .south := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      isingPrimalProjectionDivergenceWithoutNorth
        (fkIsingSquareTopBoundaryMedialObservable n hn k0)
        (fkIsingSquareBoundaryFullMedialObservable n hn
          (fullVertexSouthEdge n x hsouth))
        (fkIsingSquareTopBoundaryMedialObservable n hn k1) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.top, k1)
  let heast : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let eE := fullVertexEastEdge n x heast
  let eS := fullVertexSouthEdge n x hsouth
  let eW := fullVertexWestEdge n x hwest
  let east := fkIsingSquareTopBoundaryMedialObservable n hn k0
  let south := fkIsingSquareBoundaryFullMedialObservable n hn eS
  let west := fkIsingSquareTopBoundaryMedialObservable n hn k1
  have heE : fkIsingSquarePerimeterEdge n .top k0 = eE := by
    apply Subtype.ext
    simp only [eE, fullVertexEastEdge, fkIsingSquarePerimeterEdge,
      fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;>
      apply Subtype.ext <;> funext i <;> fin_cases i <;>
      simp [x, fkIsingSquarePerimeterDirection,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  have heW : fkIsingSquarePerimeterEdge n .top k1 = eW := rfl
  have heS : eS.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [topBoundarySouthInteriorRadialCell, eS, x, k1] using
      fkIsingSquareInteriorRadialCell_not_mem_perimeter n
        (topBoundarySouthInteriorRadialCell n hn k)
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .vertical := by
    dsimp [eS, fullVertexSouthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eS haxisS with
    ⟨_, hSE, hSS, _⟩
  have hstd := fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    n hn .top k0
  have hcomp :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .top k0
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
    isingPrimalProjectionDivergenceWithoutNorth east south west
  rw [top_boundary_vertex_laplacian_eq_increment_divergence n hn k]
  change
    (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .west)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .north))) +
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .east)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .south))) +
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .east)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .south))) = _
  simp only [fkIsingSquareBoundaryLayerInwardSide,
    fkIsingSquareBoundaryLayerEndpointSide] at hstd
  simp only [fkIsingSquareBoundaryLayerComplementInwardSide,
    fkIsingSquareBoundaryLayerComplementEndpointSide] at hcomp
  rw [heE] at hstd hcomp
  rw [hcomp, ← hstd]
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [← heE, ← heW]
  rw [← fkIsingSquareTopBoundaryMedialObservable_projection_south
        n hn k0,
      ← fkIsingSquareTopBoundaryMedialObservable_projection_east
        n hn k0,
      ← fkIsingSquareBoundaryFullMedialObservable_projection
        n hn eS heS .east,
      ← fkIsingSquareBoundaryFullMedialObservable_projection
        n hn eS heS .south,
      ← fkIsingSquareTopBoundaryMedialObservable_projection_east
        n hn k1,
      ← fkIsingSquareTopBoundaryMedialObservable_projection_south
        n hn k1,
      hSE, hSS]
  have hpairI := isingProj_normSq_add_neg Complex.I east (by norm_num)
  have hpairOne := isingProj_normSq_add_neg 1 east (by norm_num)
  change
    (Complex.normSq (isingProj Complex.I east) -
        Complex.normSq (isingProj (-1) east)) +
      (Complex.normSq (isingProj Complex.I south) -
        Complex.normSq (isingProj 1 south)) +
      (Complex.normSq (isingProj (-1) west) -
        Complex.normSq (isingProj Complex.I west)) = _
  have hEast : Complex.normSq (isingProj Complex.I east) -
        Complex.normSq (isingProj (-1) east) =
      Complex.normSq (isingProj 1 east) -
        Complex.normSq (isingProj (-Complex.I) east) := by
    linarith
  rw [hEast]
  unfold isingPrimalProjectionDivergenceWithoutNorth
  ring


theorem bottom_boundary_face_step
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let j : Fin (2 * n) := ⟨0, by omega⟩
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (k1, j) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (k0, j) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let j : Fin (2 * n) := ⟨0, by omega⟩
  let c : FKIsingSquareFullFaceNode n := (k0, j)
  let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
  let hx : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let e := fkIsingSquareDirectionEdge n x .north hx
  have hedge : faceEastEdge n c = e := by
    have hv : faceSEVertex n c = x := by
      apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [faceSEVertex, c, x, fkIsingSquareBoundaryVertex,
          fkIsingSquareBoundarySite, fkIsingSquareInteriorCellKey,
          fkIsingSquareInteriorFaceKey, k0, k1, j] <;> ring
    apply Subtype.ext
    simp only [faceEastEdge, e, fkIsingSquareDirectionEdge]
    let hface : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .north := by
      simp [fkIsingSquareDirectionAvailable, faceSEVertex, c,
        fkIsingSquareInteriorCellKey, fkIsingSquareInteriorFaceKey, j]
      exact hn
    have hnbr : fkIsingSquareNeighbor n (faceSEVertex n c) .north hface =
        fkIsingSquareNeighbor n x .north hx := by
      apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [faceSEVertex, c, x, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, fkIsingSquareBoundaryVertex,
          fkIsingSquareBoundarySite, fkIsingSquareInteriorCellKey,
          fkIsingSquareInteriorFaceKey, k0, k1, j] <;> ring
    exact congrArg₂ (fun a b => s(a, b)) hv hnbr
  have hdiff := face_difference_east n hn c (by
    have hk := k.isLt
    change k.1 + 1 < 2 * n
    omega)
  have htrans := bottom_boundary_transverse_increment_eq n hn k
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south)) at htrans
  rw [hedge] at hdiff
  have hcE : faceEastNeighbor n c (by
      have hk := k.isLt
      change k.1 + 1 < 2 * n
      omega) = (k1, j) := by
    apply Prod.ext
    · apply Fin.ext
      simp [faceEastNeighbor, c, k0, k1]
    · rfl
  rw [hcE] at hdiff
  change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
      (k1, j) = _
  change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
      (k1, j) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (k0, j) = _ at hdiff
  rw [htrans] at hdiff
  linarith


theorem right_boundary_face_step
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let i : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (i, k1) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (i, k0) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let i : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  let c : FKIsingSquareFullFaceNode n := (i, k0)
  let x := fkIsingSquareBoundaryVertex n (.right, k1)
  let hx : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let e := fkIsingSquareDirectionEdge n x .west hx
  have hedge : faceNorthEdge n c = e := by
    apply Subtype.ext
    simp only [faceNorthEdge, e, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor
    · apply Subtype.ext
      funext q
      fin_cases q <;>
        simp [faceNWVertex, c, x, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, fkIsingSquareBoundaryVertex,
          fkIsingSquareBoundarySite, fkIsingSquareInteriorCellKey,
          fkIsingSquareInteriorFaceKey, i, k0, k1] <;> omega
    · apply Subtype.ext
      funext q
      fin_cases q <;>
        simp [faceNWVertex, c, x, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, fkIsingSquareBoundaryVertex,
          fkIsingSquareBoundarySite, fkIsingSquareInteriorCellKey,
          fkIsingSquareInteriorFaceKey, i, k0, k1] <;> omega
  have hdiff := face_difference_north n hn c (by
    have hk := k.isLt
    change k.1 + 1 < 2 * n
    omega)
  have htrans := right_boundary_transverse_increment_eq n hn k
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) at htrans
  rw [hedge] at hdiff
  have hcN : faceNorthNeighbor n c (by
      have hk := k.isLt
      change k.1 + 1 < 2 * n
      omega) = (i, k1) := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp [faceNorthNeighbor, c, k0, k1]
  rw [hcN] at hdiff
  change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
      (i, k1) = _
  change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
      (i, k1) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (i, k0) = _ at hdiff
  rw [htrans] at hdiff
  linarith


theorem top_boundary_face_step
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let i0 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let i1 : Fin (2 * n) := ⟨k.1, by omega⟩
    let j : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (i0, j) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (i1, j) := by
  have hk := k.isLt
  let kp : Fin (2 * n - 1) := ⟨2 * n - 2 - k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨kp.1 + 1, by omega⟩
  let i0 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let i1 : Fin (2 * n) := ⟨k.1, by omega⟩
  let j : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  let c : FKIsingSquareFullFaceNode n := (i0, j)
  let x := fkIsingSquareBoundaryVertex n (.top, k1)
  let hx : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let e := fkIsingSquareDirectionEdge n x .south hx
  have hedge : faceWestEdge n c = e := by
    apply Subtype.ext
    simp only [faceWestEdge, e, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor
    · apply Subtype.ext
      funext q
      fin_cases q <;>
        simp [faceSWVertex, c, x, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, fkIsingSquareBoundaryVertex,
          fkIsingSquareBoundarySite, fkIsingSquareInteriorCellKey,
          fkIsingSquareInteriorFaceKey, i0, j, kp, k1] <;> omega
    · apply Subtype.ext
      funext q
      fin_cases q <;>
        simp [faceSWVertex, c, x, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, fkIsingSquareBoundaryVertex,
          fkIsingSquareBoundarySite, fkIsingSquareInteriorCellKey,
          fkIsingSquareInteriorFaceKey, i0, j, kp, k1] <;> omega
  have hi0 : 0 < i0.1 := by
    change 0 < k.1 + 1
    omega
  have hdiff := face_difference_west n hn c hi0
  have htrans := top_boundary_transverse_increment_eq n hn kp
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) at htrans
  rw [hedge] at hdiff
  have hcW : faceWestNeighbor n c hi0 = (i1, j) := by
    apply Prod.ext
    · apply Fin.ext
      simp [faceWestNeighbor, c, i0, i1]
    · rfl
  rw [hcW] at hdiff
  change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
      (i0, j) = _
  change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
      (i1, j) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (i0, j) = _ at hdiff
  rw [htrans] at hdiff
  linarith

theorem bottom_row_const
    (n : Nat) (hn : 0 < n) (i : Fin (2 * n)) :
    let z : Fin (2 * n) := ⟨0, by omega⟩
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (i, z) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (z, z) := by
  let z : Fin (2 * n) := ⟨0, by omega⟩
  have hchain : ∀ t, (ht : t < 2 * n) →
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (⟨t, ht⟩, z) =
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (z, z) := by
    intro t ht
    induction t with
    | zero => rfl
    | succ t ih =>
        have htstep : t < 2 * n - 1 := by omega
        let k : Fin (2 * n - 1) := ⟨t, htstep⟩
        have hs := bottom_boundary_face_step n hn k
        change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
            (⟨t + 1, by omega⟩, z) =
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
            (⟨t, by omega⟩, z) at hs
        exact hs.trans (ih (by omega))
  exact hchain i.1 i.2

theorem right_column_const
    (n : Nat) (hn : 0 < n) (j : Fin (2 * n)) :
    let z : Fin (2 * n) := ⟨0, by omega⟩
    let last : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (last, j) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (last, z) := by
  let z : Fin (2 * n) := ⟨0, by omega⟩
  let last : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  have hchain : ∀ t, (ht : t < 2 * n) →
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (last, ⟨t, ht⟩) =
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (last, z) := by
    intro t ht
    induction t with
    | zero => rfl
    | succ t ih =>
        have htstep : t < 2 * n - 1 := by omega
        let k : Fin (2 * n - 1) := ⟨t, htstep⟩
        have hs := right_boundary_face_step n hn k
        change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
            (last, ⟨t + 1, by omega⟩) =
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
            (last, ⟨t, by omega⟩) at hs
        exact hs.trans (ih (by omega))
  exact hchain j.1 j.2

theorem top_row_const
    (n : Nat) (hn : 0 < n) (i : Fin (2 * n)) :
    let z : Fin (2 * n) := ⟨0, by omega⟩
    let last : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (i, last) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (z, last) := by
  let z : Fin (2 * n) := ⟨0, by omega⟩
  let last : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  have hchain : ∀ t, (ht : t < 2 * n) →
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (⟨t, ht⟩, last) =
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (z, last) := by
    intro t ht
    induction t with
    | zero => rfl
    | succ t ih =>
        have htstep : t < 2 * n - 1 := by omega
        let k : Fin (2 * n - 1) := ⟨t, htstep⟩
        have hs := top_boundary_face_step n hn k
        change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
            (⟨t + 1, by omega⟩, last) =
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
            (⟨t, by omega⟩, last) at hs
        exact hs.trans (ih (by omega))
  exact hchain i.1 i.2

theorem terminalAdjacentFace_eq_topLeft
    (n : Nat) (hn : 0 < n) :
    let z : Fin (2 * n) := ⟨0, by omega⟩
    let last : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
    FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn =
      (z, last) := by
  let z : Fin (2 * n) := ⟨0, by omega⟩
  let last : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  apply fkIsingSquareInteriorCellKey_injective n
  rw [show FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn =
    fkIsingSquareFullFaceOfRadialIncidence n hn
      (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentIncidence n hn)
    from rfl, fkIsingSquareFullFaceOfRadialIncidence_key]
  change fkIsingSquareWedgeFaceKey n
      (fkIsingSquareLeftVerticalEdge n hn ⟨2 * n - 1, by omega⟩, .east) =
    fkIsingSquareInteriorCellKey n (z, last)
  simp [fkIsingSquareWedgeFaceKey, fkIsingSquareLeftVerticalEdge,
    fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
    fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation,
    fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
    fkIsingSquareNeighborSite, fkIsingSquareInteriorCellKey,
    fkIsingSquareInteriorFaceKey, z, last]


theorem boundaryLayer_terminalDart_observable
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredTerminalDart n hn)) = 1 := by
  rw [<- fkIsingSquareBoundaryLayer_fermionicObservable_incidence]
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  rw [<- D.fermionicObservable_terminal]
  unfold FKIsingDobrushinDomain.fermionicObservable
  apply Finset.sum_congr rfl
  intro omega _
  have hbmem : (.bond (fkIsingSquareWiredTerminalDart n hn) :
      FKIsingSquareWiredCarrier n) ∈ D.exploration omega := by
    exact fkIsingSquareWired_terminalBond_mem_explorationOrder n hn
      (fkIsingSquareClosePerimeter n omega)
  have htmem : (.terminal : FKIsingSquareWiredCarrier n) ∈
      D.exploration omega := D.terminal_mem omega
  change D.fermionicSummand omega
      (.bond (fkIsingSquareWiredTerminalDart n hn)) =
    D.fermionicSummand omega .terminal
  unfold FKIsingDobrushinDomain.fermionicSummand
  rw [if_pos hbmem, if_pos htmem]
  unfold FKIsingDobrushinDomain.windingPhase
  change (D.criticalMass omega : Complex) *
      Complex.exp (Complex.I *
        (((fkIsingSquareWiredLiftedWinding n hn
          (fkIsingSquareClosePerimeter n omega)
            (.bond (fkIsingSquareWiredTerminalDart n hn))) / 2 : Real) :
              Complex)) = _
  rw [show fkIsingSquareWiredLiftedWinding n hn
      (fkIsingSquareClosePerimeter n omega)
        (.bond (fkIsingSquareWiredTerminalDart n hn)) =
      fkIsingSquareWiredLiftedWinding n hn
        (fkIsingSquareClosePerimeter n omega) .terminal by
    unfold fkIsingSquareWiredLiftedWinding
      fkIsingSquareWiredPhysicalTurnCount
    rw [fkIsingSquareWired_terminalBond_rawTurnCount]]
  rfl

theorem boundaryLayer_terminalDart_increment
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquareWiredTerminalDart n hn)) = 1 := by
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [boundaryLayer_terminalDart_observable n hn]
  norm_num

theorem terminalAdjacent_bondMate_eq_topComplementEndpoint
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn
        (leftInteriorEastDart n hn ⟨2 * n - 1, by omega⟩).1 =
      (fkIsingSquarePerimeterEdge n .top
        (fkIsingSquarePerimeterLastIndex n hn), .south) := by
  let d := leftInteriorEastDart n hn ⟨2 * n - 1, by omega⟩
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d.1 d.2]
  dsimp [d, leftInteriorEastDart]
  have hdart :
      (fkIsingSquareLeftVerticalEdge n hn ⟨2 * n - 1, by omega⟩, .east) =
        fkIsingSquareDirectionDart n
          (fkIsingSquareLeftVerticalUpper n hn ⟨2 * n - 1, by omega⟩)
          .south (fkIsingSquareLeftVerticalUpper_south_available n hn _)
          .counterclockwise := by
    apply fkIsingSquareDart_key_injective n
    simp [fkIsingSquareLeftVerticalEdge, fkIsingSquareDirectionDart,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareCornerSide,
      fkIsingSquareEndpointForDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
  rw [hdart]
  change fkIsingSquareBondMate n hn
    (fkIsingSquareDirectionDart n
      (fkIsingSquareLeftVerticalUpper n hn ⟨2 * n - 1, by omega⟩)
      .south _ .counterclockwise) = _
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hdir : fkIsingSquareNextDirection n
      (fkIsingSquareLeftVerticalUpper n hn ⟨2 * n - 1, by omega⟩) .south =
      .east := by
    simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable,
      fkIsingSquareLeftVerticalUpper, hn]
  calc
    _ = fkIsingSquareDirectionDart n
        (fkIsingSquareLeftVerticalUpper n hn ⟨2 * n - 1, by omega⟩)
        .east (by simp [fkIsingSquareDirectionAvailable,
          fkIsingSquareLeftVerticalUpper]; omega) .clockwise :=
      fkIsingSquareDirectionDart_congr n _ hdir _ _ _
    _ = _ := by
      apply fkIsingSquareDart_key_injective n
      simp [fkIsingSquareDirectionDart, fkIsingSquareDartEndpoint,
        fkIsingSquareDartDirection, fkIsingSquareSideCorner,
        fkIsingSquareCornerSide, fkIsingSquareEndpointForDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquarePerimeterLastIndex,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
      · apply Subtype.ext
        funext i
        fin_cases i <;> simp <;> omega


theorem terminalAdjacentFace_eq_one (n : Nat) (hn : 0 < n) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
      (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) = 1 := by
  let last : Fin (2 * n) := fkIsingSquarePerimeterLastIndex n hn
  let d := leftInteriorEastDart n hn ⟨2 * n - 1, by omega⟩
  let e : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d
  have hmate : fkIsingSquareWiredBondMate n hn d.1 =
      (fkIsingSquarePerimeterEdge n .top last, .south) := by
    simpa [d, last] using
      terminalAdjacent_bondMate_eq_topComplementEndpoint n hn
  have hbond := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
    n hn d.1
      (fkIsingSquareInteriorRadialDart_ne_source n hn d)
      (fkIsingSquareInteriorRadialDart_ne_terminal n hn d)
  rw [hmate] at hbond
  have hcomplement :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .top last
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .top last, .west)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .top last, .south)) at hcomplement
  have hterminal := boundaryLayer_terminalDart_increment n hn
  rw [fkIsingSquareWiredTerminalDart_eq_perimeter_top_last n hn] at hterminal
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .top last, .west)) = 1 at hterminal
  have hd : fkIsingSquareBoundaryLayerRadialIncrement n hn e = 1 := by
    change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart d.1) = 1
    rw [← hbond, ← hcomplement]
    exact hterminal
  have hgap :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn e
  have hend : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareMarkedB n := by
    change fkIsingSquareDartEndpoint n
        (fkIsingSquareLeftVerticalEdge n hn
          ⟨2 * n - 1, by omega⟩, .east) = _
    unfold fkIsingSquareDartEndpoint
    simp only [fkIsingSquareSideCorner]
    change (fkIsingSquareOrientedEdge n
      (fkIsingSquareLeftVerticalEdge n hn
        ⟨2 * n - 1, by omega⟩)).head = _
    unfold fkIsingSquareLeftVerticalEdge
    rw [fkIsingSquareOrientedEdge_directionEdge]
    change fkIsingSquareLeftVerticalUpper n hn
      ⟨2 * n - 1, by omega⟩ = _
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [fkIsingSquareLeftVerticalUpper, fkIsingSquareMarkedB] <;> omega
  rw [hend, markedB_base, sub_zero, hd] at hgap
  simpa [e, d, FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace,
    FKIsingSquareFullIntegratedPrimitive.terminalAdjacentIncidence] using hgap


theorem terminalAdjacentFace_nonneg (n : Nat) (hn : 0 < n) :
    0 <= (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
      (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) := by
  let e := FKIsingSquareFullIntegratedPrimitive.terminalAdjacentIncidence n hn
  have hgap :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn e
  have hend : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareMarkedB n := by
    change fkIsingSquareDartEndpoint n
        (fkIsingSquareLeftVerticalEdge n hn
          ⟨2 * n - 1, by omega⟩, .east) = _
    unfold fkIsingSquareDartEndpoint
    simp only [fkIsingSquareSideCorner]
    change (fkIsingSquareOrientedEdge n
      (fkIsingSquareLeftVerticalEdge n hn
        ⟨2 * n - 1, by omega⟩)).head = _
    unfold fkIsingSquareLeftVerticalEdge
    rw [fkIsingSquareOrientedEdge_directionEdge]
    change fkIsingSquareLeftVerticalUpper n hn
      ⟨2 * n - 1, by omega⟩ = _
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [fkIsingSquareLeftVerticalUpper, fkIsingSquareMarkedB] <;> omega
  rw [hend, markedB_base, sub_zero] at hgap
  rw [show FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn =
      fkIsingSquareFullFaceOfRadialIncidence n hn e from rfl, hgap]
  exact fkIsingSquareBoundaryLayerRadialIncrement_nonneg n hn e


theorem terminalAdjacentFace_le_one (n : Nat) (hn : 0 < n) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
      (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) <= 1 := by
  let k : Fin (2 * n) := ⟨0, by omega⟩
  have hv : fkIsingSquareBoundaryVertex n (.left, k) =
      fkIsingSquareMarkedB n := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [k, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareMarkedB]
  have hface : FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn =
      fkIsingSquareFullFaceOfRadialIncidence n hn
        (fkIsingSquarePerimeterInteriorRadialIncidence n hn .left k) := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace,
      fkIsingSquareFullFaceOfRadialIncidence_key]
    change fkIsingSquareWedgeFaceKey n
        (fkIsingSquareLeftVerticalEdge n hn ⟨2 * n - 1, by omega⟩, .east) =
      fkIsingSquareWedgeFaceKey n
        (fkIsingSquarePerimeterInteriorRadialDart n .left k).1
    simp [fkIsingSquareWedgeFaceKey, fkIsingSquareLeftVerticalEdge,
      fkIsingSquarePerimeterInteriorRadialDart,
      fkIsingSquarePerimeterInteriorSide, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareLeftVerticalUpper,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k]
    omega
  have hgap :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_boundary_face_sub_vertex
      n hn .left k
  rw [hv, markedB_base, sub_zero] at hgap
  rw [hface, hgap]
  exact fkIsingSquareBoundaryLayerInwardIncrement_le_one n hn .left k


theorem face_fixedBoundary_eq_terminal
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n)
    (hc : fkIsingSquareFullFaceFixedBoundary n c) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) := by
  let z : Fin (2 * n) := ⟨0, by omega⟩
  let last : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  have hterminal :
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (z, last) =
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) := by
    rw [terminalAdjacentFace_eq_topLeft n hn]
  rcases hc with hbottom | hright | htop
  · have hc2 : c.2 = z := by
      apply Fin.ext
      simpa [z] using hbottom
    have hc' : c = (c.1, z) := by
      apply Prod.ext
      · rfl
      · exact hc2
    rw [hc']
    calc
      _ = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (z, z) := bottom_row_const n hn c.1
      _ = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (last, z) := (bottom_row_const n hn last).symm
      _ = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (last, last) := (right_column_const n hn last).symm
      _ = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (z, last) := top_row_const n hn last
      _ = _ := hterminal
  · have hc1 : c.1 = last := by
      apply Fin.ext
      simp [last]
      omega
    have hc' : c = (last, c.2) := by
      apply Prod.ext
      · exact hc1
      · rfl
    rw [hc']
    calc
      _ = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (last, z) := right_column_const n hn c.2
      _ = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (last, last) := (right_column_const n hn last).symm
      _ = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (z, last) := top_row_const n hn last
      _ = _ := hterminal
  · have hc2 : c.2 = last := by
      apply Fin.ext
      simp [last]
      omega
    have hc' : c = (c.1, last) := by
      apply Prod.ext
      · rfl
      · exact hc2
    rw [hc']
    calc
      _ = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (z, last) := top_row_const n hn c.1
      _ = _ := hterminal


theorem face_fixedBoundary_eq_one
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n)
    (hc : fkIsingSquareFullFaceFixedBoundary n c) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c = 1 := by
  rw [face_fixedBoundary_eq_terminal n hn c hc,
    terminalAdjacentFace_eq_one n hn]


theorem face_fixedBoundary_le_one
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n)
    (hc : fkIsingSquareFullFaceFixedBoundary n c) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c <= 1 := by
  rw [face_fixedBoundary_eq_terminal n hn c hc]
  exact terminalAdjacentFace_le_one n hn


theorem face_fixedBoundary_nonneg
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n)
    (hc : fkIsingSquareFullFaceFixedBoundary n c) :
    0 <= (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c := by
  rw [face_fixedBoundary_eq_terminal n hn c hc]
  exact terminalAdjacentFace_nonneg n hn


theorem boundaryLayer_inwardIncrement_eq_terminal_sub_vertex
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n))
    (hfree : side ≠ .left) :
    fkIsingSquareBoundaryLayerInwardIncrement n hn side k =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareBoundaryVertex n (side, k)) := by
  have hgap :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_boundary_face_sub_vertex
      n hn side k
  have hfixed := fkIsingSquarePerimeterInteriorFace_fixedBoundary_of_free
    n hn side k hfree
  rw [face_fixedBoundary_eq_terminal n hn _ hfixed] at hgap
  linarith


theorem boundaryLayer_inwardIncrement_eq_one_sub_vertex
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n))
    (hfree : side ≠ .left) :
    fkIsingSquareBoundaryLayerInwardIncrement n hn side k =
      1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareBoundaryVertex n (side, k)) := by
  rw [boundaryLayer_inwardIncrement_eq_terminal_sub_vertex
      n hn side k hfree,
    terminalAdjacentFace_eq_one n hn]


theorem freeBoundary_vertex_le_one
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n))
    (hfree : side ≠ .left) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareBoundaryVertex n (side, k)) <= 1 := by
  have hgap :=
    boundaryLayer_inwardIncrement_eq_terminal_sub_vertex
      n hn side k hfree
  have hnonneg := fkIsingSquareBoundaryLayerInwardIncrement_nonneg
    n hn side k
  have hterminal := terminalAdjacentFace_le_one n hn
  linarith


theorem boundaryLayer_halfDiagonal_eq_ghost_terminal_sub_vertex
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n))
    (hfree : side ≠ .left) :
    Real.sqrt 2 / 2 * Complex.normSq
        (fkIsingSquareBoundaryLayerVertexFermion n hn side k) =
      isingFermionicGhostCoefficient *
        ((fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
            (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) -
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
            (fkIsingSquareBoundaryVertex n (side, k))) := by
  rw [fkIsingSquareBoundaryLayer_halfDiagonal_normSq,
    boundaryLayer_inwardIncrement_eq_terminal_sub_vertex n hn side k hfree]


theorem boundaryLayer_halfDiagonal_eq_ghost_one_sub_vertex
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n))
    (hfree : side ≠ .left) :
    Real.sqrt 2 / 2 * Complex.normSq
        (fkIsingSquareBoundaryLayerVertexFermion n hn side k) =
      isingFermionicGhostCoefficient *
        (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareBoundaryVertex n (side, k))) := by
  rw [boundaryLayer_halfDiagonal_eq_ghost_terminal_sub_vertex
      n hn side k hfree,
    terminalAdjacentFace_eq_one n hn]

theorem bottom_boundary_complementIncrement_eq_terminal_sub_vertex
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .bottom k0,
          fkIsingSquareBoundaryLayerComplementInwardSide .bottom)) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareBoundaryVertex n (.bottom, k1)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let d : FKIsingSquareInteriorRadialDart n :=
    ⟨(fkIsingSquarePerimeterEdge n .bottom k0, .north), by
      simp [fkIsingSquareWedgeFaceKey, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareDartDirection, fkIsingSquareSideCorner,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey, k0]
      omega⟩
  let r : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d
  have hend : fkIsingSquareInteriorRadialEndpoint n hn r =
      fkIsingSquareBoundaryVertex n (.bottom, k1) := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [r, d, fkIsingSquareInteriorRadialEndpoint,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareSideCorner,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, k0, k1] <;> ring
  have hfaceeq : fkIsingSquareFullFaceOfRadialIncidence n hn r =
      fkIsingSquareFullFaceOfRadialIncidence n hn
        (fkIsingSquarePerimeterInteriorRadialIncidence n hn .bottom k0) := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [r, d, fkIsingSquarePerimeterInteriorRadialIncidence,
      fkIsingSquarePerimeterInteriorRadialDart,
      fkIsingSquarePerimeterInteriorSide, fkIsingSquareWedgeFaceKey,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, k0]
  have hface : fkIsingSquareFullFaceFixedBoundary n
      (fkIsingSquareFullFaceOfRadialIncidence n hn r) := by
    rw [hfaceeq]
    exact fkIsingSquarePerimeterInteriorFace_fixedBoundary_of_free
      n hn .bottom k0 (by decide)
  have hgap :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn r
  rw [hend, face_fixedBoundary_eq_terminal n hn _ hface] at hgap
  have hcomp :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .bottom k0
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .east)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .north)) at hcomp
  change _ = fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .north)) at hgap
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .east)) = _
  linarith

theorem bottom_boundary_complement_halfDiagonal_eq_ghost_terminal_sub_vertex
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    Real.sqrt 2 / 2 * Complex.normSq
        (fkIsingSquareBoundaryLayerComplementVertexFermion
          n hn .bottom k0) =
      isingFermionicGhostCoefficient *
        ((fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
            (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) -
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
            (fkIsingSquareBoundaryVertex n (.bottom, k1))) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  change Real.sqrt 2 / 2 * Complex.normSq
      (fkIsingSquareBoundaryLayerComplementVertexFermion
        n hn .bottom k0) = _
  rw [fkIsingSquareBoundaryLayerComplement_halfDiagonal_normSq]
  change isingFermionicGhostCoefficient *
      fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .east)) = _
  have hgap :=
    bottom_boundary_complementIncrement_eq_terminal_sub_vertex n hn k
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .east)) =
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) -
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareBoundaryVertex n (.bottom, k1)) at hgap
  rw [hgap]


theorem bottom_boundary_complement_halfDiagonal_eq_ghost_one_sub_vertex
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    Real.sqrt 2 / 2 * Complex.normSq
        (fkIsingSquareBoundaryLayerComplementVertexFermion
          n hn .bottom k0) =
      isingFermionicGhostCoefficient *
        (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareBoundaryVertex n (.bottom, k1))) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  change Real.sqrt 2 / 2 * Complex.normSq
      (fkIsingSquareBoundaryLayerComplementVertexFermion
        n hn .bottom k0) =
    isingFermionicGhostCoefficient *
      (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareBoundaryVertex n (.bottom, k1)))
  rw [bottom_boundary_complement_halfDiagonal_eq_ghost_terminal_sub_vertex
      n hn k,
    terminalAdjacentFace_eq_one n hn]

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
