/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundary.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareLaplacian


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem eastSouth_bondMate (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    fkIsingSquareWiredBondMate n hn (eastSouthDart n x heast hsouth).1 =
      (fullVertexSouthEdge n x hsouth, .east) := by
  have hsouth' : -(n : Int) < x.1 1 := hsouth
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _
    (eastSouthDart n x heast hsouth).2]
  apply fkIsingSquareDart_key_injective n
  simp [eastSouthDart, fullVertexEastEdge, fullVertexSouthEdge,
    fkIsingSquareBondMate, fkIsingSquarePreviousDirection,
    fkIsingSquareDirectionAvailable, hsouth', fkIsingSquareDirectionDart,
    fkIsingSquareSideCorner, fkIsingSquareCornerSide,
    fkIsingSquareEndpointForDirection]

theorem southNorth_bondMate (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (hsouth : fkIsingSquareDirectionAvailable n x .south)
    (hwest : fkIsingSquareDirectionAvailable n x .west) :
    fkIsingSquareWiredBondMate n hn (southNorthDart n x hsouth hwest).1 =
      (fullVertexWestEdge n x hwest, .east) := by
  have hwest' : -(n : Int) < x.1 0 := hwest
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _
    (southNorthDart n x hsouth hwest).2]
  apply fkIsingSquareDart_key_injective n
  simp [southNorthDart, fullVertexSouthEdge, fullVertexWestEdge,
    fkIsingSquareBondMate, fkIsingSquarePreviousDirection,
    fkIsingSquareDirectionAvailable, hwest', fkIsingSquareDirectionDart,
    fkIsingSquareSideCorner, fkIsingSquareCornerSide,
    fkIsingSquareEndpointForDirection]

theorem westNorth_bondMate (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hnorth : fkIsingSquareDirectionAvailable n x .north) :
    fkIsingSquareWiredBondMate n hn (westNorthDart n x hwest hnorth).1 =
      (fullVertexNorthEdge n x hnorth, .west) := by
  have hnorth' : x.1 1 < (n : Int) := hnorth
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _
    (westNorthDart n x hwest hnorth).2]
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
    _ = (fullVertexNorthEdge n x hnorth, .west) := rfl

theorem fkIsingSquareFullVertexFullObservable_quad (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareWiredFullMedialObservable n hn
        (fullVertexSouthEdge n x hsouth))
      (fkIsingSquareWiredFullMedialObservable n hn
        (fullVertexWestEdge n x hwest))
      (fkIsingSquareWiredFullMedialObservable n hn
        (fullVertexNorthEdge n x hnorth))
      (fkIsingSquareWiredFullMedialObservable n hn
        (fullVertexEastEdge n x heast)) := by
  let eN := fullVertexNorthEdge n x hnorth
  let eE := fullVertexEastEdge n x heast
  let eS := fullVertexSouthEdge n x hsouth
  let eW := fullVertexWestEdge n x hwest
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .vertical := by
    dsimp [eN, fullVertexNorthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
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
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eN haxisN with
    ⟨hNW, _, hNS, _⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eE haxisE with
    ⟨hEW, _, hES, _⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eS haxisS with
    ⟨_, hSE, _, hSN⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eW haxisW with
    ⟨_, hWE, _, hWN⟩
  have hNEobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) := by
    let d := northSouthDart n x hnorth heast
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eE, .west) := by
      simpa [d, eE] using (show
        fkIsingSquareWiredBondMate n hn (northSouthDart n x hnorth heast).1 =
          (fullVertexEastEdge n x heast, .west) by
            have heast' : x.1 0 < (n : Int) := heast
            rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _
              (northSouthDart n x hnorth heast).2]
            apply fkIsingSquareDart_key_injective n
            simp [northSouthDart, fullVertexNorthEdge, fullVertexEastEdge,
              fkIsingSquareBondMate, fkIsingSquarePreviousDirection,
              fkIsingSquareDirectionAvailable, heast',
              fkIsingSquareDirectionDart, fkIsingSquareSideCorner,
              fkIsingSquareCornerSide, fkIsingSquareEndpointForDirection])
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
      simp [d, northSouthDart, eN, hcE.1, hcN.2.2.1, Int.ModEq]
    have h :=
      fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart d.1) at h
    rw [hmate] at h
    simpa [d, northSouthDart, eN] using h.symm
  have hESobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .south)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .east)) := by
    let d := eastSouthDart n x heast hsouth
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eS, .east) := by
      simpa [d, eS] using eastSouth_bondMate n hn x heast hsouth
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
      simp [d, eastSouthDart, eE, hcE.2.2.1, hcS.2.1, Int.ModEq]
    have h :=
      fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart d.1) at h
    rw [hmate] at h
    simpa [d, eastSouthDart, eE] using h.symm
  have hSWobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := by
    let d := southNorthDart n x hsouth hwest
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eW, .east) := by
      simpa [d, eW] using southNorth_bondMate n hn x hsouth hwest
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
      simp [d, southNorthDart, eS, hcS.2.2.2, hcW.2.1, Int.ModEq]
    have h :=
      fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart d.1) at h
    rw [hmate] at h
    simpa [d, southNorthDart, eS] using h.symm
  have hWNobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .north)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .west)) := by
    let d := westNorthDart n x hwest hnorth
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eN, .west) := by
      simpa [d, eN] using westNorth_bondMate n hn x hwest hnorth
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
      simp [d, westNorthDart, eW, hcW.2.2.2, hcN.1, Int.ModEq]
    have h :=
      fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart d.1) at h
    rw [hmate] at h
    simpa [d, westNorthDart, eW] using h.symm
  let north := fkIsingSquareWiredFullMedialObservable n hn eN
  let east := fkIsingSquareWiredFullMedialObservable n hn eE
  let south := fkIsingSquareWiredFullMedialObservable n hn eS
  let west := fkIsingSquareWiredFullMedialObservable n hn eW
  change IsingSquareSHolomorphicQuad south west north east
  apply isingSquareSHolomorphicQuad_of_projection_cycle north east south west
  · calc
      isingProj 1 north = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .south)))
          north := by rw [hNS]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) := by
        simpa [north] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eN .south
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) := hNEobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eE, .west)))
          east := by
        symm
        simpa [east] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eE .west
      _ = isingProj 1 east := by rw [hEW]
  · calc
      isingProj Complex.I east = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eE, .south)))
          east := by rw [hES]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .south)) := by
        simpa [east] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eE .south
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .east)) := hESobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .east)))
          south := by
        symm
        simpa [south] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eS .east
      _ = isingProj Complex.I south := by rw [hSE]
  · calc
      isingProj (-1) south = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .north)))
          south := by rw [hSN]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) := by
        simpa [south] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eS .north
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := hSWobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .east)))
          west := by
        symm
        simpa [west] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eW .east
      _ = isingProj (-1) west := by rw [hWE]
  · calc
      isingProj (-Complex.I) west = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .north)))
          west := by rw [hWN]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .north)) := by
        simpa [west] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eW .north
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .west)) := hWNobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .west)))
          north := by
        symm
        simpa [north] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eN .west
      _ = isingProj (-Complex.I) north := by rw [hNW]

theorem fkIsingSquareFullVertex_neighborFinset
    (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    (fkSquareBoxPlanar n).G.neighborFinset x =
      {fkIsingSquareNeighbor n x .east heast,
        fkIsingSquareNeighbor n x .north hnorth,
        fkIsingSquareNeighbor n x .west hwest,
        fkIsingSquareNeighbor n x .south hsouth} := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hxy
    change (hypercubicLattice 2).Adj x.1 y.1 at hxy
    rcases adj_neighbor_cases x.1 y.1 hxy with h | h | h | h
    · right; right; left
      apply Subtype.ext
      funext k
      fin_cases k
      · have hk := congrFun h 0
        simp [Pi.add_apply] at hk
        change y.1 0 = x.1 0 - 1
        omega
      · have hk := congrFun h 1
        simp [Pi.add_apply] at hk
        simpa [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] using hk.symm
    · left
      apply Subtype.ext
      funext k
      fin_cases k
      · have hk := congrFun h 0
        simp [Pi.add_apply] at hk
        change y.1 0 = x.1 0 + 1
        omega
      · have hk := congrFun h 1
        simp [Pi.add_apply] at hk
        simpa [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] using hk.symm
    · right; right; right
      apply Subtype.ext
      funext k
      fin_cases k
      · have hk := congrFun h 0
        simp [Pi.add_apply] at hk
        simpa [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] using hk.symm
      · have hk := congrFun h 1
        simp [Pi.add_apply] at hk
        change y.1 1 = x.1 1 - 1
        omega
    · right; left
      apply Subtype.ext
      funext k
      fin_cases k
      · have hk := congrFun h 0
        simp [Pi.add_apply] at hk
        simpa [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] using hk.symm
      · have hk := congrFun h 1
        simp [Pi.add_apply] at hk
        change y.1 1 = x.1 1 + 1
        omega
  · rintro (rfl | rfl | rfl | rfl)
    · exact fkIsingSquare_adj_neighbor n x .east heast
    · exact fkIsingSquare_adj_neighbor n x .north hnorth
    · exact fkIsingSquare_adj_neighbor n x .west hwest
    · exact fkIsingSquare_adj_neighbor n x .south hsouth

theorem vertex_difference_of_common_face
    (n : Nat) (hn : 0 < n)
    (e f : FKIsingSquareInteriorRadialIncidence n hn)
    (hface : fkIsingSquareFullFaceOfRadialIncidence n hn e =
      fkIsingSquareFullFaceOfRadialIncidence n hn f) :
    FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
          (fkIsingSquareInteriorRadialEndpoint n hn f) -
        FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
          (fkIsingSquareInteriorRadialEndpoint n hn e) =
      fkIsingSquareInteriorRadialIncrement n hn e -
        fkIsingSquareInteriorRadialIncrement n hn f := by
  have he := FKIsingSquareFullIntegratedPrimitive.face_sub_vertex n hn e
  have hf := FKIsingSquareFullIntegratedPrimitive.face_sub_vertex n hn f
  rw [hface] at he
  linarith

end
end StatMech.Universality
