/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part9


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem fkIsingSquareBottomBoundaryObservable_quad
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
    let hnorth : fkIsingSquareDirectionAvailable n x .north := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBottomBoundaryMissingSouthObservable n hn k)
      (fkIsingSquareBottomBoundaryMedialObservable n hn k0)
      (fkIsingSquareBoundaryFullMedialObservable n hn
        (fullVertexNorthEdge n x hnorth))
      (fkIsingSquareBottomBoundaryMedialObservable n hn k1) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
  let heast : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let eN := fullVertexNorthEdge n x hnorth
  let eE := fullVertexEastEdge n x heast
  let eW := fullVertexWestEdge n x hwest
  have heE : fkIsingSquarePerimeterEdge n .bottom k1 = eE := rfl
  have heW : fkIsingSquarePerimeterEdge n .bottom k0 = eW := by
    apply Subtype.ext
    simp only [eW, fullVertexWestEdge, fkIsingSquarePerimeterEdge,
      fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor
    · apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [x, fkIsingSquarePerimeterDirection,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
          fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
    · apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [x, fkIsingSquarePerimeterDirection,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
          fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  have heN : eN.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [bottomBoundaryNorthInteriorRadialCell, eN, x, k1] using
      fkIsingSquareInteriorRadialCell_not_mem_perimeter n
        (bottomBoundaryNorthInteriorRadialCell n hn k)
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .vertical := by
    dsimp [eN, fullVertexNorthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisE : (fkIsingSquareOrientedEdge n eE).axis = .horizontal := by
    dsimp [eE, fullVertexEastEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .horizontal := by
    dsimp [eW, fullVertexWestEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eN haxisN with
    ⟨hNW, _, hNS, _⟩
  have hNEobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) := by
    let d : FKIsingSquareInteriorRadialDart n :=
      ⟨(eN, .south), (bottomBoundaryNorthInteriorRadialCell n hn k).2 .south⟩
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eE, .west) := by
      have heast' : x.1 0 < (n : Int) := heast
      rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _ d.2]
      apply fkIsingSquareDart_key_injective n
      simp [d, eN, eE, fullVertexNorthEdge, fullVertexEastEdge,
        fkIsingSquareBondMate, fkIsingSquarePreviousDirection,
        fkIsingSquareDirectionAvailable, heast', fkIsingSquareDirectionDart,
        fkIsingSquareSideCorner, fkIsingSquareCornerSide,
        fkIsingSquareEndpointForDirection]
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcE := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eE haxisE
      have hcN := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eN haxisN
      change fkIsingSquareWiredDirectedTangentCode n hn (.bond (eE, .west)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond (eN, .south)) [ZMOD 8]
      rw [hcE.1, hcN.2.2.1]
      decide
    have h :=
      fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquareWiredBondMate n hn d.1)) = _ at h
    rw [hmate] at h
    simpa [d] using h.symm
  have hWNobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .north)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .west)) := by
    let d : FKIsingSquareInteriorRadialDart n :=
      ⟨(eW, .north), by
        rw [← heW]
        simp [fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
          fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
          fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
          fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
          fkIsingSquareDirectionEdgeOrientation,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
          fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0]
        omega⟩
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eN, .west) := by
      have hnorth' : x.1 1 < (n : Int) := hnorth
      rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _ d.2]
      change fkIsingSquareBondMate n hn
        (fkIsingSquareDirectionDart n x .west hwest .clockwise) = _
      simp only [fkIsingSquareBondMate,
        fkIsingSquareDirectionDart_endpoint,
        fkIsingSquareDirectionDart_direction,
        fkIsingSquareDirectionDart_turn]
      have hdir : fkIsingSquarePreviousDirection n x .west = .north := by
        simp [fkIsingSquarePreviousDirection,
          fkIsingSquareDirectionAvailable, hnorth']
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
      have hcW := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eW haxisW
      have hcN := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eN haxisN
      change fkIsingSquareWiredDirectedTangentCode n hn (.bond (eN, .west)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond (eW, .north)) [ZMOD 8]
      rw [hcN.1, hcW.2.2.2]
      decide
    have h :=
      fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquareWiredBondMate n hn d.1)) = _ at h
    rw [hmate] at h
    simpa [d] using h.symm
  let north := fkIsingSquareBoundaryFullMedialObservable n hn eN
  let east := fkIsingSquareBottomBoundaryMedialObservable n hn k1
  let south := fkIsingSquareBottomBoundaryMissingSouthObservable n hn k
  let west := fkIsingSquareBottomBoundaryMedialObservable n hn k0
  change IsingSquareSHolomorphicQuad south west north east
  apply isingSquareSHolomorphicQuad_of_projection_cycle north east south west
  · calc
      isingProj 1 north = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .south)))
          north := by rw [hNS]
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) := by
        simpa [north] using
          fkIsingSquareBoundaryFullMedialObservable_projection
            n hn eN heN .south
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) := hNEobs
      _ = isingProj 1 east := by
        rw [← heE]
        simpa [east] using
          (fkIsingSquareBottomBoundaryMedialObservable_projection_west
            n hn k1).symm
  · simpa [south, east] using
      (fkIsingSquareBottomBoundaryMissingSouthObservable_projection_east
        n hn k).symm
  · simpa [south, west] using
      fkIsingSquareBottomBoundaryMissingSouthObservable_projection_west n hn k
  · calc
      isingProj (-Complex.I) west =
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eW, .north)) := by
        rw [← heW]
        simpa [west] using
          fkIsingSquareBottomBoundaryMedialObservable_projection_north n hn k0
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .west)) := hWNobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .west)))
          north := by
        symm
        simpa [north] using
          fkIsingSquareBoundaryFullMedialObservable_projection
            n hn eN heN .west
      _ = isingProj (-Complex.I) north := by rw [hNW]

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
