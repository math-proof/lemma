/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part16


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem right_boundary_projection_cycle
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.right, k1)
    let hwest : fkIsingSquareDirectionAvailable n x .west := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    let north := fkIsingSquareRightBoundaryMedialObservable n hn k1
    let south := fkIsingSquareRightBoundaryMedialObservable n hn k0
    let west := fkIsingSquareBoundaryFullMedialObservable n hn
      (fullVertexWestEdge n x hwest)
    isingProj (-1) south = isingProj (-1) west ∧
      isingProj (-Complex.I) west = isingProj (-Complex.I) north := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.right, k1)
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let eW := fullVertexWestEdge n x hwest
  let eN := fullVertexNorthEdge n x hnorth
  let eS := fullVertexSouthEdge n x hsouth
  have heN : fkIsingSquarePerimeterEdge n .right k1 = eN := rfl
  have heS : fkIsingSquarePerimeterEdge n .right k0 = eS := by
    apply Subtype.ext
    simp only [eS, fullVertexSouthEdge, fkIsingSquarePerimeterEdge,
      fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;>
      apply Subtype.ext <;> funext i <;> fin_cases i <;>
      simp [x, fkIsingSquarePerimeterDirection,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  have heW : eW.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [rightBoundaryWestInteriorRadialCell, eW, x, k1] using
      fkIsingSquareInteriorRadialCell_not_mem_perimeter n
        (rightBoundaryWestInteriorRadialCell n hn k)
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .horizontal := by
    dsimp [eW, fullVertexWestEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .vertical := by
    dsimp [eN, fullVertexNorthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .vertical := by
    dsimp [eS, fullVertexSouthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eW haxisW with
    ⟨_, hWE, _, hWN⟩
  have hSWobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := by
    let d : FKIsingSquareInteriorRadialDart n := ⟨(eW, .east),
      (rightBoundaryWestInteriorRadialCell n hn k).2 .east⟩
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eS, .north) := by
      rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _ d.2]
      change fkIsingSquareBondMate n hn
        (fkIsingSquareDirectionDart n x .west hwest .counterclockwise) = _
      simp only [fkIsingSquareBondMate,
        fkIsingSquareDirectionDart_endpoint,
        fkIsingSquareDirectionDart_direction,
        fkIsingSquareDirectionDart_turn]
      have hdir : fkIsingSquareNextDirection n x .west = .south := by
        simp [fkIsingSquareNextDirection, hsouth]
      calc
        _ = fkIsingSquareDirectionDart n x .south hsouth .clockwise :=
          fkIsingSquareDirectionDart_congr n x hdir _ _ _
        _ = (eS, .north) := by
          rw [← heS]
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
      have hcS := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eS haxisS
      have hcW := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eW haxisW
      change fkIsingSquareWiredDirectedTangentCode n hn (.bond (eS, .north)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond (eW, .east)) [ZMOD 8]
      rw [hcS.2.2.2, hcW.2.1]
      decide
    have h := fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
      n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) = _ at h
    rw [hmate] at h
    simpa [d] using h
  have hWNobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .north)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .west)) := by
    let d : FKIsingSquareInteriorRadialDart n := ⟨(eW, .north),
      (rightBoundaryWestInteriorRadialCell n hn k).2 .north⟩
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eN, .west) := by
      rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _ d.2]
      change fkIsingSquareBondMate n hn
        (fkIsingSquareDirectionDart n x .west hwest .clockwise) = _
      simp only [fkIsingSquareBondMate,
        fkIsingSquareDirectionDart_endpoint,
        fkIsingSquareDirectionDart_direction,
        fkIsingSquareDirectionDart_turn]
      have hdir : fkIsingSquarePreviousDirection n x .west = .north := by
        simp [fkIsingSquarePreviousDirection, hnorth]
      calc
        _ = fkIsingSquareDirectionDart n x .north hnorth .counterclockwise :=
          fkIsingSquareDirectionDart_congr n x hdir _ _ _
        _ = (eN, .west) := rfl
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcN := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eN haxisN
      have hcW := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eW haxisW
      change fkIsingSquareWiredDirectedTangentCode n hn (.bond (eN, .west)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond (eW, .north)) [ZMOD 8]
      rw [hcN.1, hcW.2.2.2]
      decide
    have h := fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
      n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) = _ at h
    rw [hmate] at h
    simpa [d] using h.symm
  let north := fkIsingSquareRightBoundaryMedialObservable n hn k1
  let south := fkIsingSquareRightBoundaryMedialObservable n hn k0
  let west := fkIsingSquareBoundaryFullMedialObservable n hn eW
  constructor
  · calc
      isingProj (-1) south =
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eS, .north)) := by
        rw [← heS]
        simpa [south] using
          fkIsingSquareRightBoundaryMedialObservable_projection_north n hn k0
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := hSWobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .east)))
          west := by
        symm
        simpa [west] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eW heW .east
      _ = isingProj (-1) west := by rw [hWE]
  · calc
      isingProj (-Complex.I) west = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .north)))
          west := by rw [hWN]
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .north)) := by
        simpa [west] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eW heW .north
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .west)) := hWNobs
      _ = isingProj (-Complex.I) north := by
        rw [← heN]
        simpa [north] using
          (fkIsingSquareRightBoundaryMedialObservable_projection_west
            n hn k1).symm


theorem right_boundary_vertex_laplacian_eq_increment_divergence
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.right, k1)
    let hnorth : fkIsingSquareDirectionAvailable n x .north := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
      omega
    let hsouth : fkIsingSquareDirectionAvailable n x .south := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    let hwest : fkIsingSquareDirectionAvailable n x .west := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    let eN := fullVertexNorthEdge n x hnorth
    let eS := fullVertexSouthEdge n x hsouth
    let eW := fullVertexWestEdge n x hwest
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .west)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .north))) +
        (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .east)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .south))) +
        (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .east)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .south))) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.right, k1)
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let xN := fkIsingSquareNeighbor n x .north hnorth
  let xS := fkIsingSquareNeighbor n x .south hsouth
  let xW := fkIsingSquareNeighbor n x .west hwest
  let eN := fullVertexNorthEdge n x hnorth
  let eS := fullVertexSouthEdge n x hsouth
  let eW := fullVertexWestEdge n x hwest
  let H := (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
  have hneighbors : (fkSquareBoxPlanar n).G.neighborFinset x =
      {xN, xS, xW} := by
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
      · have hi := congrFun h 0
        simp [Pi.add_apply, x, fkIsingSquareBoundaryVertex,
          fkIsingSquareBoundarySite] at hi
        have hy := fkIsingSquareVertex_coordinate_bounds n y 0
        omega
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
    · rintro (rfl | rfl | rfl)
      · exact fkIsingSquare_adj_neighbor n x .north hnorth
      · exact fkIsingSquare_adj_neighbor n x .south hsouth
      · exact fkIsingSquare_adj_neighbor n x .west hwest
  have hNS : xN ≠ xS := by
    intro h
    have h1 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 1) h
    simp [xN, xS, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h1
  have hNW : xN ≠ xW := by
    intro h
    have h1 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 1) h
    simp [xN, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h1
  have hSW : xS ≠ xW := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) h
    simp [xS, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hLap : isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x =
      (H xN - H x) + (H xS - H x) + (H xW - H x) := by
    unfold isingFiniteGraphLaplacian
    rw [hneighbors]
    simp [hNS, hNW, hSW]
    ring
  have hdN := vertex_difference_north n hn x hnorth hwest
  have hdW := vertex_difference_west n hn x hwest hsouth
  have hdS := right_boundary_vertex_difference_south n hn k
  change H xN - H x = _ at hdN
  change H xW - H x = _ at hdW
  have hx0 : fkIsingSquareBoundaryVertex n (.right, k0) = xS := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [xS, x, fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k0, k1] <;> ring
  have heS : fkIsingSquarePerimeterEdge n .right k0 = eS := by
    apply Subtype.ext
    simp only [eS, fullVertexSouthEdge, fkIsingSquarePerimeterEdge,
      fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;>
      apply Subtype.ext <;> funext i <;> fin_cases i <;>
      simp [x, fkIsingSquarePerimeterDirection,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  change H (fkIsingSquareBoundaryVertex n (.right, k0)) - H x = _ at hdS
  rw [hx0, heS] at hdS
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x = _
  rw [hLap, hdN, hdS, hdW]


theorem right_boundary_vertex_laplacian_eq_projectionDivergenceWithoutEast
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.right, k1)
    let hwest : fkIsingSquareDirectionAvailable n x .west := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      isingPrimalProjectionDivergenceWithoutEast
        (fkIsingSquareRightBoundaryMedialObservable n hn k1)
        (fkIsingSquareRightBoundaryMedialObservable n hn k0)
        (fkIsingSquareBoundaryFullMedialObservable n hn
          (fullVertexWestEdge n x hwest)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.right, k1)
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let eN := fullVertexNorthEdge n x hnorth
  let eS := fullVertexSouthEdge n x hsouth
  let eW := fullVertexWestEdge n x hwest
  let north := fkIsingSquareRightBoundaryMedialObservable n hn k1
  let south := fkIsingSquareRightBoundaryMedialObservable n hn k0
  let west := fkIsingSquareBoundaryFullMedialObservable n hn eW
  have heN : fkIsingSquarePerimeterEdge n .right k1 = eN := rfl
  have heS : fkIsingSquarePerimeterEdge n .right k0 = eS := by
    apply Subtype.ext
    simp only [eS, fullVertexSouthEdge, fkIsingSquarePerimeterEdge,
      fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;>
      apply Subtype.ext <;> funext i <;> fin_cases i <;>
      simp [x, fkIsingSquarePerimeterDirection,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  have heW : eW.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [rightBoundaryWestInteriorRadialCell, eW, x, k1] using
      fkIsingSquareInteriorRadialCell_not_mem_perimeter n
        (rightBoundaryWestInteriorRadialCell n hn k)
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .horizontal := by
    dsimp [eW, fullVertexWestEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eW haxisW with
    ⟨_, hWE, hWS, _⟩
  have hstd := fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    n hn .right k0
  have hcomp :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .right k0
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
    isingPrimalProjectionDivergenceWithoutEast north south west
  rw [right_boundary_vertex_laplacian_eq_increment_divergence n hn k]
  change
    (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .west)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .north))) +
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .east)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .south))) +
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .east)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .south))) = _
  simp only [fkIsingSquareBoundaryLayerInwardSide,
    fkIsingSquareBoundaryLayerEndpointSide] at hstd
  simp only [fkIsingSquareBoundaryLayerComplementInwardSide,
    fkIsingSquareBoundaryLayerComplementEndpointSide] at hcomp
  rw [heS] at hstd hcomp
  rw [hcomp, ← hstd]
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [← heN, ← heS]
  rw [← fkIsingSquareRightBoundaryMedialObservable_projection_west
        n hn k1,
      ← fkIsingSquareRightBoundaryMedialObservable_projection_north
        n hn k1,
      ← fkIsingSquareRightBoundaryMedialObservable_projection_north
        n hn k0,
      ← fkIsingSquareRightBoundaryMedialObservable_projection_west
        n hn k0,
      ← fkIsingSquareBoundaryFullMedialObservable_projection
        n hn eW heW .east,
      ← fkIsingSquareBoundaryFullMedialObservable_projection
        n hn eW heW .south,
      hWE, hWS]
  have hpairI := isingProj_normSq_add_neg Complex.I south (by norm_num)
  have hpairOne := isingProj_normSq_add_neg 1 south (by norm_num)
  change
    (Complex.normSq (isingProj (-Complex.I) north) -
        Complex.normSq (isingProj (-1) north)) +
      (Complex.normSq (isingProj (-1) south) -
        Complex.normSq (isingProj (-Complex.I) south)) +
      (Complex.normSq (isingProj (-1) west) -
        Complex.normSq (isingProj Complex.I west)) = _
  have hSouth : Complex.normSq (isingProj (-1) south) -
        Complex.normSq (isingProj (-Complex.I) south) =
      Complex.normSq (isingProj Complex.I south) -
        Complex.normSq (isingProj 1 south) := by
    linarith
  rw [hSouth]
  unfold isingPrimalProjectionDivergenceWithoutEast
  ring


theorem top_boundary_transverse_increment_eq
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.top, k1)
    let hx : fkIsingSquareDirectionAvailable n x .south := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    let e := fkIsingSquareDirectionEdge n x .south hx
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.top, k1)
  let hx : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let e := fkIsingSquareDirectionEdge n x .south hx
  let heast : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let dE : FKIsingSquareInteriorRadialDart n := ⟨(e, .east), by
    simp [e, x, fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorFaceKey, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, k1, hn]
    omega⟩
  let dN : FKIsingSquareInteriorRadialDart n := ⟨(e, .north), by
    simp [e, x, fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorFaceKey, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, k1, hn]
    omega⟩
  have hmateE : fkIsingSquareWiredBondMate n hn dE.1 =
      (fkIsingSquarePerimeterEdge n .top k0, .south) := by
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn dE.1 dE.2]
    change fkIsingSquareBondMate n hn
      (fkIsingSquareDirectionDart n x .south hx .counterclockwise) = _
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir : fkIsingSquareNextDirection n x .south = .east := by
      simp [fkIsingSquareNextDirection, heast]
    calc
      _ = fkIsingSquareDirectionDart n x .east heast .clockwise :=
        fkIsingSquareDirectionDart_congr n x hdir _ _ _
      _ = (fkIsingSquarePerimeterEdge n .top k0, .south) := by
        apply fkIsingSquareDart_key_injective n
        have htargetEndpoint :
            fkIsingSquareDartEndpoint n
                (fkIsingSquarePerimeterEdge n .top k0, .south) = x := by
          apply Subtype.ext
          funext i
          fin_cases i <;>
            simp [x, fkIsingSquarePerimeterEdge,
              fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
              fkIsingSquareOrientedEdge_directionEdge,
              fkIsingSquareDirectionEdgeOrientation,
              fkIsingSquareSideCorner, fkIsingSquareBoundaryVertex,
              fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
              fkIsingSquareNeighborSite, k0, k1] <;> ring
        have htargetDirection :
            fkIsingSquareDartDirection n
                (fkIsingSquarePerimeterEdge n .top k0, .south) = .east := by
          simp [fkIsingSquarePerimeterEdge,
            fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
            fkIsingSquareOrientedEdge_directionEdge,
            fkIsingSquareDirectionEdgeOrientation,
            fkIsingSquareSideCorner]
        simp only [fkIsingSquareDirectionDart_endpoint,
          fkIsingSquareDirectionDart_direction]
        rw [htargetEndpoint, htargetDirection]
        simp [fkIsingSquareDirectionDart,
          fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
  have hmateN : fkIsingSquareWiredBondMate n hn dN.1 =
      (fkIsingSquarePerimeterEdge n .top k1, .east) := by
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn dN.1 dN.2]
    change fkIsingSquareBondMate n hn
      (fkIsingSquareDirectionDart n x .south hx .clockwise) = _
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir : fkIsingSquarePreviousDirection n x .south = .west := by
      simp [fkIsingSquarePreviousDirection, hwest]
    calc
      _ = fkIsingSquareDirectionDart n x .west hwest .counterclockwise :=
        fkIsingSquareDirectionDart_congr n x hdir _ _ _
      _ = (fkIsingSquarePerimeterEdge n .top k1, .east) := rfl
  have hE := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
    n hn dE.1
      (fkIsingSquareInteriorRadialDart_ne_source n hn dE)
      (fkIsingSquareInteriorRadialDart_ne_terminal n hn dE)
  have hN := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
    n hn dN.1
      (fkIsingSquareInteriorRadialDart_ne_source n hn dN)
      (fkIsingSquareInteriorRadialDart_ne_terminal n hn dN)
  rw [hmateE] at hE
  rw [hmateN] at hN
  have hprev :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .top k0
  have hnext := fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    n hn .top k1
  let dC : FKIsingMedialDart (fkSquareBoxPlanar n) :=
    (fkIsingSquarePerimeterEdge n .top k0, .west)
  have hdCout : dC ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
    rintro ⟨i, hi⟩
    have hwire :=
      fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
    have hend := congrArg (fkIsingSquareDartEndpoint n) hi
    change fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBoundaryDart n hn i) =
      fkIsingSquareDartEndpoint n dC at hend
    rw [hend] at hwire
    simp [dC, fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k0] at hwire
    simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hwire
    omega
  have hmateC : fkIsingSquareWiredBondMate n hn dC =
      (fkIsingSquarePerimeterEdge n .top k1, .north) := by
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
      n hn dC hdCout]
    have hprevEdge : fkIsingSquareDartEndpoint n dC = x := by
      apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [dC, x, fkIsingSquarePerimeterEdge,
          fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
          fkIsingSquareOrientedEdge_directionEdge,
          fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
          fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
    have hdirection : fkIsingSquareDartDirection n dC = .east := by
      simp [dC, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
    have hdCrepr : dC =
        fkIsingSquareDirectionDart n x .east heast .counterclockwise := by
      apply fkIsingSquareDart_key_injective n
      simp only [fkIsingSquareDirectionDart_endpoint,
        fkIsingSquareDirectionDart_direction]
      rw [hprevEdge, hdirection]
      simp [dC, fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
    rw [hdCrepr]
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir : fkIsingSquareNextDirection n x .east = .west := by
      simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable,
        x, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      omega
    calc
      _ = fkIsingSquareDirectionDart n x .west hwest .clockwise :=
        fkIsingSquareDirectionDart_congr n x hdir _ _ _
      _ = (fkIsingSquarePerimeterEdge n .top k1, .north) := rfl
  have hdCsource : dC ≠ fkIsingSquareWiredSourceDart n hn := by
    intro h
    have hs := congrArg Prod.snd h
    simp [dC, fkIsingSquareWiredSourceDart,
      fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide] at hs
  have hdCterminal : dC ≠ fkIsingSquareWiredTerminalDart n hn := by
    intro h
    have he := congrArg
      (fun d => (fkIsingSquareDartEndpoint n d).1 0) h
    simp [dC, fkIsingSquareWiredTerminalDart,
      fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide,
      fkIsingSquareDartEndpoint, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
      fkIsingSquareMarkedB, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, k0] at he
    have hk := k.isLt
    omega
  have hC := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
    n hn dC hdCsource hdCterminal
  rw [hmateC] at hC
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east))
  exact hN.symm.trans (hnext.trans (hC.trans (hprev.trans hE)))

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
