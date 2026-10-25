/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareFaceLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareLaplacian.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part6


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem faceEastWest_bondMate (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareWiredBondMate n hn (faceEastWestDart n c).1 =
      (faceSouthEdge n c, .north) := by
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _
    (faceEastWestDart n c).2]
  change fkIsingSquareBondMate n hn
    (fkIsingSquareDirectionDart n (faceSEVertex n c) .north
      (faceSE_north_available n c) .counterclockwise) = _
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hwest : -(n : Int) < (faceSEVertex n c).1 0 :=
    faceSE_west_available n c
  have hdir : fkIsingSquareNextDirection n (faceSEVertex n c) .north = .west := by
    simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable, hwest]
  calc
    _ = fkIsingSquareDirectionDart n (faceSEVertex n c) .west
        (faceSE_west_available n c) .clockwise :=
      fkIsingSquareDirectionDart_congr n _ hdir _ _ _
    _ = (fkIsingSquareDirectionEdge n (faceSEVertex n c) .west
          (faceSE_west_available n c), .north) := rfl
    _ = (faceSouthEdge n c, .north) := by rw [faceSouthEdge_eq_west]

theorem fkIsingSquareFullFaceFullObservable_quad (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareWiredFullMedialObservable n hn (faceNorthEdge n c))
      (fkIsingSquareWiredFullMedialObservable n hn (faceEastEdge n c))
      (fkIsingSquareWiredFullMedialObservable n hn (faceSouthEdge n c))
      (fkIsingSquareWiredFullMedialObservable n hn (faceWestEdge n c)) := by
  let eN := faceNorthEdge n c
  let eE := faceEastEdge n c
  let eS := faceSouthEdge n c
  let eW := faceWestEdge n c
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
    ⟨hNW, hNE, hNS, hNN⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eE haxisE with
    ⟨hEW, hEE, hES, hEN⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eS haxisS with
    ⟨hSW, hSE, hSS, hSN⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eW haxisW with
    ⟨hWW, hWE, hWS, hWN⟩
  have hSWobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .west)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .south)) := by
    let d := faceSouthWestDart n c
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eW, .south) := by
      simpa [d, eW] using faceSouthWest_bondMate n hn c
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcS := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eS haxisS
      have hcW := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eW haxisW
      simp [d, faceSouthWestDart, eS, hcS.1, hcW.2.2.1, Int.ModEq]
    have h :=
      fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart d.1) at h
    rw [hmate] at h
    simpa [d, faceSouthWestDart, eS] using h.symm
  have hWNobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) := by
    let d := faceWestEastDart n c
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eN, .south) := by
      simpa [d, eN] using faceWestEast_bondMate n hn c
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcW := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eW haxisW
      have hcN := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eN haxisN
      simp [d, faceWestEastDart, eW, hcW.2.1, hcN.2.2.1, Int.ModEq]
    have h :=
      fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart d.1) at h
    rw [hmate] at h
    simpa [d, faceWestEastDart, eW] using h.symm
  have hNEobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .east)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .north)) := by
    let d := faceNorthEastDart n c
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eE, .north) := by
      simpa [d, eE] using faceNorthEast_bondMate n hn c
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcN := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eN haxisN
      have hcE := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eE haxisE
      simp [d, faceNorthEastDart, eN, hcN.2.1, hcE.2.2.2, Int.ModEq]
    have h :=
      fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart d.1) at h
    rw [hmate] at h
    simpa [d, faceNorthEastDart, eN] using h.symm
  have hESobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) := by
    let d := faceEastWestDart n c
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eS, .north) := by
      simpa [d, eS] using faceEastWest_bondMate n hn c
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcE := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eE haxisE
      have hcS := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eS haxisS
      simp [d, faceEastWestDart, eE, hcE.1, hcS.2.2.2, Int.ModEq]
    have h :=
      fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart d.1) at h
    rw [hmate] at h
    simpa [d, faceEastWestDart, eE] using h.symm
  let north := fkIsingSquareWiredFullMedialObservable n hn eN
  let east := fkIsingSquareWiredFullMedialObservable n hn eE
  let south := fkIsingSquareWiredFullMedialObservable n hn eS
  let west := fkIsingSquareWiredFullMedialObservable n hn eW
  change IsingSquareSHolomorphicQuad north east south west
  apply isingSquareSHolomorphicQuad_of_projection_cycle south west north east
  · calc
      isingProj 1 south = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .west))) south := by
        rw [hSW]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .west)) := by
        simpa [south] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eS .west
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .south)) := hSWobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .south))) west := by
        symm
        simpa [west] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eW .south
      _ = isingProj 1 west := by rw [hWS]
  · calc
      isingProj Complex.I west = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .east))) west := by
        rw [hWE]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := by
        simpa [west] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eW .east
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) := hWNobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .south))) north := by
        symm
        simpa [north] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eN .south
      _ = isingProj Complex.I north := by rw [hNS]
  · calc
      isingProj (-1) north = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .east))) north := by
        rw [hNE]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .east)) := by
        simpa [north] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eN .east
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .north)) := hNEobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eE, .north))) east := by
        symm
        simpa [east] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eE .north
      _ = isingProj (-1) east := by rw [hEN]
  · calc
      isingProj (-Complex.I) east = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eE, .west))) east := by
        rw [hEW]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) := by
        simpa [east] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eE .west
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) := hESobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .north))) south := by
        symm
        simpa [south] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eS .north
      _ = isingProj (-Complex.I) south := by rw [hSN]

end
end StatMech.Universality
