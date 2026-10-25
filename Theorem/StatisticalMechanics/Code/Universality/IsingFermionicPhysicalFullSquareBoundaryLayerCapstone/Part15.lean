/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part14


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem left_boundary_interior_increment_eq
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    fkIsingSquareBoundaryLayerRadialIncrement n hn
        (Quot.mk _ (leftInteriorEastDart n hn k)) =
      fkIsingSquareBoundaryLayerRadialIncrement n hn
        (Quot.mk _ (leftInteriorSouthDart n hn k)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquareLeftVerticalEdge n hn k
  let j : Fin (2 * n) := ⟨2 * n - 1 - k.1, by omega⟩
  have hv : fkIsingSquareBoundaryVertex n (.left, j) =
      fkIsingSquareLeftVerticalUpper n hn k := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [j, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareLeftVerticalUpper] <;> omega
  have hperim : fkIsingSquarePerimeterEdge n .left j = e := by
    apply Subtype.ext
    change s(fkIsingSquareBoundaryVertex n (.left, j),
        fkIsingSquareNeighbor n
          (fkIsingSquareBoundaryVertex n (.left, j)) .south _) =
      s(fkIsingSquareLeftVerticalUpper n hn k,
        fkIsingSquareNeighbor n
          (fkIsingSquareLeftVerticalUpper n hn k) .south _)
    rw [Sym2.eq_iff]
    apply Or.inl
    refine ⟨hv, ?_⟩
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [j, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;> omega
  have hwestNorth :
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) =
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) := by
    let w := fkIsingSquareWiredBoundaryDart n hn (.west k)
    have hw : w = (e, .west) := by
      apply Prod.ext
      · apply Subtype.ext
        change s(fkIsingSquareLeftVerticalLower n hn k,
            fkIsingSquareNeighbor n
              (fkIsingSquareLeftVerticalLower n hn k) .north
              (fkIsingSquareLeftVerticalLower_north_available n hn k)) =
          s(fkIsingSquareLeftVerticalUpper n hn k,
            fkIsingSquareNeighbor n
              (fkIsingSquareLeftVerticalUpper n hn k) .south
              (fkIsingSquareLeftVerticalUpper_south_available n hn k))
        rw [Sym2.eq_iff]
        apply Or.inr
        constructor <;>
          apply Subtype.ext <;>
          funext i <;>
          fin_cases i <;>
          simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
            fkIsingSquareLeftVerticalLower,
            fkIsingSquareLeftVerticalUpper]
      · rfl
    have hnorth : fkIsingSquareWiredBondMate n hn w = (e, .north) := by
      rw [fkIsingSquareWiredBondMate_west]
      rfl
    have hsource : w ≠ fkIsingSquareWiredSourceDart n hn := by
      intro h
      have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
      cases hi
    have hterminal : w ≠ fkIsingSquareWiredTerminalDart n hn := by
      intro h
      have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
      cases hi
    have h := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
      n hn w hsource hterminal
    rw [hnorth, hw] at h
    exact h.symm
  have heastNorth :
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) =
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) := by
    unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
    change Complex.normSq (D.fermionicObservable (.dart (e, .east))) =
      Complex.normSq (D.fermionicObservable (.dart (e, .north)))
    rw [<- hperim]
    have hobs := fkIsingSquareBoundaryLayer_fermionicObservable_endpoint
      n hn .left j
    have hobs' : D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .left j, .north)) =
        D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .left j, .east)) *
            isingLambda⁻¹ := by
      simpa only [D, fkIsingSquareBoundaryLayerEndpointSide,
        fkIsingSquareBoundaryLayerInwardSide] using hobs
    rw [hobs']
    change Complex.normSq _ = Complex.normSq (_ * isingLambda⁻¹)
    rw [Complex.normSq_mul]
    have hlam : Complex.normSq isingLambda⁻¹ = 1 := by
      rw [isingLambda_inv_val]
      norm_num [Complex.normSq_apply]
    rw [hlam, mul_one]
  have hwestSouth :
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) =
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south)) := by
    unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
    change Complex.normSq (D.fermionicObservable (.dart (e, .west))) =
      Complex.normSq (D.fermionicObservable (.dart (e, .south)))
    rw [<- hperim]
    have hobs :=
      fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint
        n hn .left j
    have hobs' : D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .left j, .south)) =
        D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .left j, .west)) *
            isingLambda⁻¹ := by
      simpa only [D, fkIsingSquareBoundaryLayerComplementEndpointSide,
        fkIsingSquareBoundaryLayerComplementInwardSide] using hobs
    rw [hobs']
    change Complex.normSq _ = Complex.normSq (_ * isingLambda⁻¹)
    rw [Complex.normSq_mul]
    have hlam : Complex.normSq isingLambda⁻¹ = 1 := by
      rw [isingLambda_inv_val]
      norm_num [Complex.normSq_apply]
    rw [hlam, mul_one]
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south))
  exact heastNorth.trans (hwestNorth.symm.trans hwestSouth)

theorem leftWiredBoundaryDart_bondPhase
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    fkIsingSquareWiredBondPhase n hn
      (fkIsingSquareWiredBoundaryDart n hn (.west k)) = -isingLambda := by
  let d := fkIsingSquareWiredBoundaryDart n hn (.west k)
  have hfwd : fkIsingSquareWiredBoundaryForward n hn d
      (fkIsingSquareWiredBondMate n hn d) := by
    right
    refine ⟨k, rfl, ?_⟩
    exact fkIsingSquareWiredBondMate_west n hn k
  unfold fkIsingSquareWiredBondPhase
  rw [fkIsingSquareWiredBondTurn, if_pos hfwd, isingLambda]
  rw [show Complex.I * ((((-6 : Int) : Real) *
      (Real.pi / 8) : Real) : Complex) =
      (Real.pi / 4 : Real) * Complex.I - Real.pi * Complex.I by
        push_cast
        ring]
  rw [Complex.exp_sub, Complex.exp_pi_mul_I]
  ring


theorem left_boundary_endpoint_observable_phase
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    let e := fkIsingSquareLeftVerticalEdge n hn k
    let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
    D.fermionicObservable (.dart (e, .south)) =
      isingLambda * D.fermionicObservable (.dart (e, .east)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquareLeftVerticalEdge n hn k
  let j : Fin (2 * n) := ⟨2 * n - 1 - k.1, by omega⟩
  let w := fkIsingSquareWiredBoundaryDart n hn (.west k)
  have hperim : fkIsingSquarePerimeterEdge n .left j = e := by
    apply Subtype.ext
    change s(fkIsingSquareBoundaryVertex n (.left, j),
        fkIsingSquareNeighbor n
          (fkIsingSquareBoundaryVertex n (.left, j)) .south _) =
      s(fkIsingSquareLeftVerticalUpper n hn k,
        fkIsingSquareNeighbor n
          (fkIsingSquareLeftVerticalUpper n hn k) .south _)
    rw [Sym2.eq_iff]
    apply Or.inl
    constructor <;>
      apply Subtype.ext <;>
      funext i <;>
      fin_cases i <;>
      simp [j, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;> omega
  have hw : w = (e, .west) := by
    apply Prod.ext
    · apply Subtype.ext
      change s(fkIsingSquareLeftVerticalLower n hn k,
          fkIsingSquareNeighbor n
            (fkIsingSquareLeftVerticalLower n hn k) .north _) =
        s(fkIsingSquareLeftVerticalUpper n hn k,
          fkIsingSquareNeighbor n
            (fkIsingSquareLeftVerticalUpper n hn k) .south _)
      rw [Sym2.eq_iff]
      apply Or.inr
      constructor <;>
        apply Subtype.ext <;>
        funext i <;>
        fin_cases i <;>
        simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
          fkIsingSquareLeftVerticalLower,
          fkIsingSquareLeftVerticalUpper]
    · rfl
  have hnorth : fkIsingSquareWiredBondMate n hn w = (e, .north) := by
    rw [fkIsingSquareWiredBondMate_west]
    rfl
  have hsource : w ≠ fkIsingSquareWiredSourceDart n hn := by
    intro h
    have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
    cases hi
  have hterminal : w ≠ fkIsingSquareWiredTerminalDart n hn := by
    intro h
    have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
    cases hi
  have hbond := fkIsingSquareBoundaryLayer_fermionicObservable_bondMate
    n hn w hsource hterminal
  have hnorthWest : D.fermionicObservable (.dart (e, .north)) =
      D.fermionicObservable (.dart (e, .west)) * (-isingLambda) := by
    change D.fermionicObservable
        (.bond (fkIsingSquareWiredBondMate n hn w)) =
      D.fermionicObservable (.bond w) *
        fkIsingSquareWiredBondPhase n hn w at hbond
    rw [hnorth, leftWiredBoundaryDart_bondPhase n hn k] at hbond
    simpa only [D, hw, fkIsingSquareBoundaryLayer_fermionicObservable_incidence]
      using hbond
  have hnorthEast : D.fermionicObservable (.dart (e, .north)) =
      D.fermionicObservable (.dart (e, .east)) * isingLambda⁻¹ := by
    rw [← hperim]
    simpa only [D, fkIsingSquareBoundaryLayerEndpointSide,
      fkIsingSquareBoundaryLayerInwardSide] using
      fkIsingSquareBoundaryLayer_fermionicObservable_endpoint n hn .left j
  have hwestEast : D.fermionicObservable (.dart (e, .west)) =
      isingLambda ^ 2 * D.fermionicObservable (.dart (e, .east)) := by
    rw [hnorthEast] at hnorthWest
    field_simp [isingLambda_ne] at hnorthWest ⊢
    ring_nf at hnorthWest ⊢
    have hlam4 : isingLambda ^ 4 = -1 := by
      rw [show isingLambda ^ 4 = (isingLambda ^ 2) ^ 2 by ring,
        isingLambda_sq]
      norm_num [Complex.I_sq]
    rw [hnorthWest]
    symm
    calc
      isingLambda ^ 2 *
          -(isingLambda ^ 2 * D.fermionicObservable (.dart (e, .west))) =
        -(isingLambda ^ 4) *
          D.fermionicObservable (.dart (e, .west)) := by ring
      _ = D.fermionicObservable (.dart (e, .west)) := by rw [hlam4]; ring
  have hsouthWest : D.fermionicObservable (.dart (e, .south)) =
      D.fermionicObservable (.dart (e, .west)) * isingLambda⁻¹ := by
    rw [← hperim]
    simpa only [D, fkIsingSquareBoundaryLayerComplementEndpointSide,
      fkIsingSquareBoundaryLayerComplementInwardSide] using
      fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint
        n hn .left j
  change D.fermionicObservable (.dart (e, .south)) =
    isingLambda * D.fermionicObservable (.dart (e, .east))
  rw [hsouthWest, hwestEast]
  field_simp [isingLambda_ne]

theorem faceSouthWest_observable_eq
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (faceSouthEdge n c, .west)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (faceWestEdge n c, .south)) := by
  let d := faceSouthWestDart n c
  have hmate : fkIsingSquareWiredBondMate n hn d.1 =
      (faceWestEdge n c, .south) := by
    simpa [d] using faceSouthWest_bondMate n hn c
  have haxisS : (fkIsingSquareOrientedEdge n (faceSouthEdge n c)).axis =
      .horizontal := by
    dsimp [faceSouthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n (faceWestEdge n c)).axis =
      .vertical := by
    dsimp [faceWestEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hcode : fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
    change fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
    rw [hmate]
    have hcS := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
      n hn (faceSouthEdge n c) haxisS
    have hcW := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
      n hn (faceWestEdge n c) haxisW
    simp [d, faceSouthWestDart, hcS.1, hcW.2.2.1, Int.ModEq]
  have h := fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
    n hn d hcode
  change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart d.1) at h
  rw [hmate] at h
  simpa [d, faceSouthWestDart] using h.symm

theorem faceWestNorth_observable_eq
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (faceWestEdge n c, .east)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (faceNorthEdge n c, .south)) := by
  let d := faceWestEastDart n c
  have hmate : fkIsingSquareWiredBondMate n hn d.1 =
      (faceNorthEdge n c, .south) := by
    simpa [d] using faceWestEast_bondMate n hn c
  have haxisW : (fkIsingSquareOrientedEdge n (faceWestEdge n c)).axis =
      .vertical := by
    dsimp [faceWestEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisN : (fkIsingSquareOrientedEdge n (faceNorthEdge n c)).axis =
      .horizontal := by
    dsimp [faceNorthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hcode : fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
    change fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
    rw [hmate]
    have hcW := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
      n hn (faceWestEdge n c) haxisW
    have hcN := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
      n hn (faceNorthEdge n c) haxisN
    simp [d, faceWestEastDart, hcW.2.1, hcN.2.2.1, Int.ModEq]
  have h := fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
    n hn d hcode
  change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart d.1) at h
  rw [hmate] at h
  simpa [d, faceWestEastDart] using h.symm

theorem faceNorthEast_observable_eq
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (faceNorthEdge n c, .east)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (faceEastEdge n c, .north)) := by
  let d := faceNorthEastDart n c
  have hmate : fkIsingSquareWiredBondMate n hn d.1 =
      (faceEastEdge n c, .north) := by
    simpa [d] using faceNorthEast_bondMate n hn c
  have haxisN : (fkIsingSquareOrientedEdge n (faceNorthEdge n c)).axis =
      .horizontal := by
    dsimp [faceNorthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisE : (fkIsingSquareOrientedEdge n (faceEastEdge n c)).axis =
      .vertical := by
    dsimp [faceEastEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hcode : fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
    change fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
    rw [hmate]
    have hcN := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
      n hn (faceNorthEdge n c) haxisN
    have hcE := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
      n hn (faceEastEdge n c) haxisE
    simp [d, faceNorthEastDart, hcN.2.1, hcE.2.2.2, Int.ModEq]
  have h := fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
    n hn d hcode
  change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart d.1) at h
  rw [hmate] at h
  simpa [d, faceNorthEastDart] using h.symm

theorem faceEastSouth_observable_eq
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (faceEastEdge n c, .west)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (faceSouthEdge n c, .north)) := by
  let d := faceEastWestDart n c
  have hmate : fkIsingSquareWiredBondMate n hn d.1 =
      (faceSouthEdge n c, .north) := by
    simpa [d] using faceEastWest_bondMate n hn c
  have haxisE : (fkIsingSquareOrientedEdge n (faceEastEdge n c)).axis =
      .vertical := by
    dsimp [faceEastEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n (faceSouthEdge n c)).axis =
      .horizontal := by
    dsimp [faceSouthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hcode : fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
    change fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
    rw [hmate]
    have hcE := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
      n hn (faceEastEdge n c) haxisE
    have hcS := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
      n hn (faceSouthEdge n c) haxisS
    simp [d, faceEastWestDart, hcE.1, hcS.2.2.2, Int.ModEq]
  have h := fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
    n hn d hcode
  change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart d.1) at h
  rw [hmate] at h
  simpa [d, faceEastWestDart] using h.symm


theorem wiredArc_vertex_step
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareLeftVerticalLower n hn k) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareLeftVerticalUpper n hn k) := by
  let east : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (leftInteriorEastDart n hn k)
  let south : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (leftInteriorSouthDart n hn k)
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn east =
      fkIsingSquareFullFaceOfRadialIncidence n hn south := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    change fkIsingSquareWedgeFaceKey n
        (fkIsingSquareLeftVerticalEdge n hn k, .east) =
      fkIsingSquareWedgeFaceKey n
        (fkIsingSquareLeftVerticalEdge n hn k, .south)
    simp [fkIsingSquareWedgeFaceKey, fkIsingSquareLeftVerticalEdge,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
  have h := vertex_eq_of_common_face_increment_eq n hn south east hface.symm
    (left_boundary_interior_increment_eq n hn k).symm
  change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareLeftVerticalEdge n hn k, .south)) =
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareLeftVerticalEdge n hn k, .east)) at h
  simpa [fkIsingSquareLeftVerticalEdge, fkIsingSquareDartEndpoint,
    fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
    fkIsingSquareNeighborSite, fkIsingSquareLeftVerticalLower,
    fkIsingSquareLeftVerticalUpper] using h

theorem wiredArc_lower_const
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareLeftVerticalLower n hn k) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareLeftVerticalLower n hn ⟨0, by omega⟩) := by
  let H := (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
  let P : Nat -> Prop := fun j => forall hj : j < 2 * n,
    H (fkIsingSquareLeftVerticalLower n hn ⟨j, hj⟩) =
      H (fkIsingSquareLeftVerticalLower n hn ⟨0, by omega⟩)
  have hP : forall j, P j := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
        intro hj
        have hstep := wiredArc_vertex_step n hn ⟨j, by omega⟩
        have heq : fkIsingSquareLeftVerticalUpper n hn ⟨j, by omega⟩ =
            fkIsingSquareLeftVerticalLower n hn ⟨j + 1, hj⟩ := by
          apply Subtype.ext
          funext i
          fin_cases i <;>
            simp [fkIsingSquareLeftVerticalUpper,
              fkIsingSquareLeftVerticalLower] <;> ring
        change H _ = H _ at hstep
        rw [heq] at hstep
        exact hstep.symm.trans (ih (by omega))
  exact hP k.val k.isLt

theorem wiredArc_lower_zero
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareLeftVerticalLower n hn k) = 0 := by
  let last : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  have hlast := wiredArc_vertex_step n hn last
  have hupper : fkIsingSquareLeftVerticalUpper n hn last =
      fkIsingSquareMarkedB n := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [last, fkIsingSquareLeftVerticalUpper,
        fkIsingSquareMarkedB] <;> omega
  rw [hupper, markedB_base] at hlast
  calc
    _ = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareLeftVerticalLower n hn last) := by
        rw [wiredArc_lower_const n hn k,
          wiredArc_lower_const n hn last]
    _ = 0 := hlast

theorem vertex_fixedBoundary_eq_zero
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareFullVertexNode n)
    (hx : fkIsingSquareFullVertexFixedBoundary n x) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x = 0 := by
  have hx0 : x.1 0 = -(n : Int) := hx
  have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
  by_cases htop : x.1 1 = (n : Int)
  · have heq : x = fkIsingSquareMarkedB n := by
      apply Subtype.ext
      funext i
      fin_cases i
      · simpa [fkIsingSquareMarkedB] using hx0
      · simpa [fkIsingSquareMarkedB] using htop
    rw [heq, markedB_base]
  · let j : Nat := (x.1 1 + (n : Int)).toNat
    have hj0 : 0 <= x.1 1 + (n : Int) := by omega
    have hj : j < 2 * n := by
      rw [show j = Int.toNat (x.1 1 + (n : Int)) from rfl,
        Int.toNat_lt] <;> omega
    let k : Fin (2 * n) := ⟨j, hj⟩
    have heq : x = fkIsingSquareLeftVerticalLower n hn k := by
      apply Subtype.ext
      funext i
      fin_cases i
      · simpa [k, j, fkIsingSquareLeftVerticalLower] using hx0
      · simp [k, j, fkIsingSquareLeftVerticalLower,
          Int.toNat_of_nonneg hj0]
    rw [heq, wiredArc_lower_zero]

theorem vertex_fixedBoundary_nonneg
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareFullVertexNode n)
    (hx : fkIsingSquareFullVertexFixedBoundary n x) :
    0 <= (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x := by
  rw [vertex_fixedBoundary_eq_zero n hn x hx]


theorem bottom_boundary_transverse_increment_eq
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
    let hx : fkIsingSquareDirectionAvailable n x .north := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    let e := fkIsingSquareDirectionEdge n x .north hx
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
  let hx : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let e := fkIsingSquareDirectionEdge n x .north hx
  let heast : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let dW : FKIsingSquareInteriorRadialDart n := ⟨(e, .west), by
    simp [e, x, fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorFaceKey, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, k1, hn]
    omega⟩
  let dS : FKIsingSquareInteriorRadialDart n := ⟨(e, .south), by
    simp [e, x, fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorFaceKey, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, k1, hn]
    omega⟩
  have hmateW : fkIsingSquareWiredBondMate n hn dW.1 =
      (fkIsingSquarePerimeterEdge n .bottom k0, .north) := by
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn dW.1 dW.2]
    change fkIsingSquareBondMate n hn
      (fkIsingSquareDirectionDart n x .north hx .counterclockwise) = _
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir : fkIsingSquareNextDirection n x .north = .west := by
      simp [fkIsingSquareNextDirection, hwest]
    calc
      _ = fkIsingSquareDirectionDart n x .west hwest .clockwise :=
        fkIsingSquareDirectionDart_congr n x hdir _ _ _
      _ = (fkIsingSquarePerimeterEdge n .bottom k0, .north) := by
        apply fkIsingSquareDart_key_injective n
        have htargetEndpoint :
            fkIsingSquareDartEndpoint n
                (fkIsingSquarePerimeterEdge n .bottom k0, .north) = x := by
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
                (fkIsingSquarePerimeterEdge n .bottom k0, .north) = .west := by
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
  have hmateS : fkIsingSquareWiredBondMate n hn dS.1 =
      (fkIsingSquarePerimeterEdge n .bottom k1, .west) := by
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn dS.1 dS.2]
    change fkIsingSquareBondMate n hn
      (fkIsingSquareDirectionDart n x .north hx .clockwise) = _
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir : fkIsingSquarePreviousDirection n x .north = .east := by
      simp [fkIsingSquarePreviousDirection, heast]
    calc
      _ = fkIsingSquareDirectionDart n x .east heast .counterclockwise :=
        fkIsingSquareDirectionDart_congr n x hdir _ _ _
      _ = (fkIsingSquarePerimeterEdge n .bottom k1, .west) := rfl
  have hW := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
    n hn dW.1
      (fkIsingSquareInteriorRadialDart_ne_source n hn dW)
      (fkIsingSquareInteriorRadialDart_ne_terminal n hn dW)
  have hS := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
    n hn dS.1
      (fkIsingSquareInteriorRadialDart_ne_source n hn dS)
      (fkIsingSquareInteriorRadialDart_ne_terminal n hn dS)
  rw [hmateW] at hW
  rw [hmateS] at hS
  have hprev :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .bottom k0
  have hnext := fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    n hn .bottom k1
  let dE : FKIsingMedialDart (fkSquareBoxPlanar n) :=
    (fkIsingSquarePerimeterEdge n .bottom k0, .east)
  have hdEout : dE ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
    rintro ⟨i, hi⟩
    have hwire :=
      fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
    have hend := congrArg (fkIsingSquareDartEndpoint n) hi
    change fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBoundaryDart n hn i) =
      fkIsingSquareDartEndpoint n dE at hend
    rw [hend] at hwire
    simp [dE, fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k0] at hwire
    simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hwire
    omega
  have hmateE : fkIsingSquareWiredBondMate n hn dE =
      (fkIsingSquarePerimeterEdge n .bottom k1, .south) := by
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
      n hn dE hdEout]
    have hprevEdge : fkIsingSquareDartEndpoint n dE = x := by
      apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [dE, x, fkIsingSquarePerimeterEdge,
          fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
          fkIsingSquareOrientedEdge_directionEdge,
          fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
          fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
    have hdirection : fkIsingSquareDartDirection n dE = .west := by
      simp [dE, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
    have hturn : (fkIsingSquareSideCorner dE.2).2 = .counterclockwise := by
      rfl
    have hdErepr : dE =
        fkIsingSquareDirectionDart n x .west hwest .counterclockwise := by
      apply fkIsingSquareDart_key_injective n
      simp only [fkIsingSquareDirectionDart_endpoint,
        fkIsingSquareDirectionDart_direction]
      rw [hprevEdge, hdirection]
      simp [dE, fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
    rw [hdErepr]
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir : fkIsingSquareNextDirection n x .west = .east := by
      simp [fkIsingSquareNextDirection, heast,
        fkIsingSquareDirectionAvailable, x,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      omega
    calc
      _ = fkIsingSquareDirectionDart n x .east heast .clockwise :=
        fkIsingSquareDirectionDart_congr n x hdir _ _ _
      _ = (fkIsingSquarePerimeterEdge n .bottom k1, .south) := rfl
  have hdEsource : dE ≠ fkIsingSquareWiredSourceDart n hn := by
    intro h
    have hs := congrArg Prod.snd h
    simp [dE, fkIsingSquareWiredSourceDart,
      fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide] at hs
  have hdEterminal : dE ≠ fkIsingSquareWiredTerminalDart n hn := by
    intro h
    have hs := congrArg Prod.snd h
    simp [dE, fkIsingSquareWiredTerminalDart,
      fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide] at hs
  have hE := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
    n hn dE hdEsource hdEterminal
  rw [hmateE] at hE
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south))
  exact hW.symm.trans
    (hprev.symm.trans (hE.symm.trans (hnext.symm.trans hS)))


theorem bottom_boundary_vertex_difference_west
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x0 := fkIsingSquareBoundaryVertex n (.bottom, k0)
    let x1 := fkIsingSquareBoundaryVertex n (.bottom, k1)
    let e := fkIsingSquarePerimeterEdge n .bottom k0
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x0 -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x1 =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x0 := fkIsingSquareBoundaryVertex n (.bottom, k0)
  let x1 := fkIsingSquareBoundaryVertex n (.bottom, k1)
  let ep := fkIsingSquarePerimeterEdge n .bottom k0
  let d0 : FKIsingSquareInteriorRadialDart n := ⟨(ep, .west), by
    simp [ep, fkIsingSquareWedgeFaceKey, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey, k0]
    omega⟩
  let d1 : FKIsingSquareInteriorRadialDart n := ⟨(ep, .north), by
    simp [ep, fkIsingSquareWedgeFaceKey, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey, k0]
    omega⟩
  let r0 : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d0
  let r1 : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d1
  have hend0 : fkIsingSquareInteriorRadialEndpoint n hn r0 = x0 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [r0, d0, ep, x0, fkIsingSquareInteriorRadialEndpoint,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareSideCorner,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, k0]
  have hend1 : fkIsingSquareInteriorRadialEndpoint n hn r1 = x1 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [r1, d1, ep, x1, fkIsingSquareInteriorRadialEndpoint,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareSideCorner,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, k0, k1] <;> ring
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn r0 =
      fkIsingSquareFullFaceOfRadialIncidence n hn r1 := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [r0, r1, d0, d1, ep, fkIsingSquareWedgeFaceKey,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, k0] <;> ring_nf
  have h0 :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn r0
  have h1 :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn r1
  rw [hend0, hface] at h0
  rw [hend1] at h1
  change _ = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .west)) at h0
  change _ = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .north)) at h1
  linarith


theorem bottom_boundary_vertex_laplacian_eq_increment_divergence
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
    let he : fkIsingSquareDirectionAvailable n x .east := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
      omega
    let hnorth : fkIsingSquareDirectionAvailable n x .north := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    let hw : fkIsingSquareDirectionAvailable n x .west := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    let eE := fullVertexEastEdge n x he
    let eN := fullVertexNorthEdge n x hnorth
    let eW := fullVertexWestEdge n x hw
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .west)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .north))) +
        (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .west)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .north))) +
        (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .north)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .west))) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
  let he : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hw : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let xE := fkIsingSquareNeighbor n x .east he
  let xN := fkIsingSquareNeighbor n x .north hnorth
  let xW := fkIsingSquareNeighbor n x .west hw
  let eE := fullVertexEastEdge n x he
  let eN := fullVertexNorthEdge n x hnorth
  let eW := fullVertexWestEdge n x hw
  let H := (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
  have hneighbors : (fkSquareBoxPlanar n).G.neighborFinset x =
      {xE, xN, xW} := by
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
      · have hi := congrFun h 1
        simp [Pi.add_apply, x, fkIsingSquareBoundaryVertex,
          fkIsingSquareBoundarySite] at hi
        have hy := fkIsingSquareVertex_coordinate_bounds n y 1
        omega
      · right; left
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
      · exact fkIsingSquare_adj_neighbor n x .east he
      · exact fkIsingSquare_adj_neighbor n x .north hnorth
      · exact fkIsingSquare_adj_neighbor n x .west hw
  have hEN : xE ≠ xN := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) h
    simp [xE, xN, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hEW : xE ≠ xW := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) h
    simp [xE, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hNW : xN ≠ xW := by
    intro h
    have h1 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 1) h
    simp [xN, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h1
  have hLap : isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x =
      (H xE - H x) + (H xN - H x) + (H xW - H x) := by
    unfold isingFiniteGraphLaplacian
    rw [hneighbors]
    simp [hEN, hEW, hNW]
    ring
  have hdE := vertex_difference_east n hn x he hnorth
  have hdN := vertex_difference_north n hn x hnorth hw
  have hdW := bottom_boundary_vertex_difference_west n hn k
  change H xE - H x = _ at hdE
  change H xN - H x = _ at hdN
  have hx0 : fkIsingSquareBoundaryVertex n (.bottom, k0) = xW := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [xW, x, fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k0, k1] <;> ring
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
  change H (fkIsingSquareBoundaryVertex n (.bottom, k0)) - H x = _ at hdW
  rw [hx0, heW] at hdW
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x =
    (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .west)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .north))) +
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .west)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .north))) +
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .north)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .west)))
  rw [hLap, hdE, hdN, hdW]


theorem bottom_boundary_vertex_laplacian_eq_projectionDivergenceWithoutSouth
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
    let hnorth : fkIsingSquareDirectionAvailable n x .north := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    let eN := fullVertexNorthEdge n x hnorth
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      isingPrimalProjectionDivergenceWithoutSouth
        (fkIsingSquareBoundaryFullMedialObservable n hn eN)
        (fkIsingSquareBottomBoundaryMedialObservable n hn k1)
        (fkIsingSquareBottomBoundaryMedialObservable n hn k0) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
  let he : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hw : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let eE := fullVertexEastEdge n x he
  let eN := fullVertexNorthEdge n x hnorth
  let eW := fullVertexWestEdge n x hw
  let FN := fkIsingSquareBoundaryFullMedialObservable n hn eN
  let FE := fkIsingSquareBottomBoundaryMedialObservable n hn k1
  let FW := fkIsingSquareBottomBoundaryMedialObservable n hn k0
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
    isingPrimalProjectionDivergenceWithoutSouth FN FE FW
  have heE : fkIsingSquarePerimeterEdge n .bottom k1 = eE := by
    rfl
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
    have he' := he
    have hw' := hw
    simp [fkIsingSquareDirectionAvailable] at he' hw'
    intro hper
    simp only [fkIsingSquarePerimeterPrimalEdgeFinset, Finset.mem_biUnion,
      Finset.mem_univ, true_and, Finset.mem_image] at hper
    obtain ⟨side, j, hj⟩ := hper
    have hedge : fkIsingSquarePerimeterEdge n side j = eN :=
      Subtype.ext hj
    cases side with
    | bottom =>
        have haxis := congrArg
          (fun e => (fkIsingSquareOrientedEdge n e).axis) hedge
        change (fkIsingSquareOrientedEdge n
            (fkIsingSquarePerimeterEdge n .bottom j)).axis =
          (fkIsingSquareOrientedEdge n eN).axis at haxis
        rw [fkIsingSquarePerimeterEdge_axis] at haxis
        have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .vertical := by
          dsimp [eN, fullVertexNorthEdge]
          rw [fkIsingSquareOrientedEdge_directionEdge]
          rfl
        rw [haxisN] at haxis
        contradiction
    | top =>
        have haxis := congrArg
          (fun e => (fkIsingSquareOrientedEdge n e).axis) hedge
        change (fkIsingSquareOrientedEdge n
            (fkIsingSquarePerimeterEdge n .top j)).axis =
          (fkIsingSquareOrientedEdge n eN).axis at haxis
        rw [fkIsingSquarePerimeterEdge_axis] at haxis
        have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .vertical := by
          dsimp [eN, fullVertexNorthEdge]
          rw [fkIsingSquareOrientedEdge_directionEdge]
          rfl
        rw [haxisN] at haxis
        contradiction
    | right =>
        simp only [fkIsingSquarePerimeterEdge, fkIsingSquareDirectionEdge,
          eN, fullVertexNorthEdge] at hj
        rw [Sym2.eq_iff] at hj
        rcases hj with ⟨hbase, _⟩ | ⟨_, hnext⟩
        · have h0 := congrArg
            (fun z : (fkSquareBoxPlanar n).V => z.1 0) hbase
          simp [fkIsingSquareBoundaryVertex,
            fkIsingSquareBoundarySite] at h0
          omega
        · have h0 := congrArg
            (fun z : (fkSquareBoxPlanar n).V => z.1 0) hnext
          simp [fkIsingSquarePerimeterDirection,
            fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
            fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
          omega
    | left =>
        simp only [fkIsingSquarePerimeterEdge, fkIsingSquareDirectionEdge,
          eN, fullVertexNorthEdge] at hj
        rw [Sym2.eq_iff] at hj
        rcases hj with ⟨hbase, _⟩ | ⟨_, hnext⟩
        · have h0 := congrArg
            (fun z : (fkSquareBoxPlanar n).V => z.1 0) hbase
          simp [fkIsingSquareBoundaryVertex,
            fkIsingSquareBoundarySite] at h0
          omega
        · have h0 := congrArg
            (fun z : (fkSquareBoxPlanar n).V => z.1 0) hnext
          simp [fkIsingSquarePerimeterDirection,
            fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
            fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
          omega
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .vertical := by
    dsimp [eN, fullVertexNorthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eN haxisN with
    ⟨htNW, _, _, htNN⟩
  have hpairI := isingProj_normSq_add_neg (-Complex.I) FW (by norm_num)
  have hpairOne := isingProj_normSq_add_neg 1 FW (by norm_num)
  simp only [neg_neg] at hpairI
  have hwestRewrite :
      Complex.normSq (isingProj (-Complex.I) FW) -
          Complex.normSq (isingProj 1 FW) =
        Complex.normSq (isingProj (-1) FW) -
          Complex.normSq (isingProj Complex.I FW) := by
    linarith
  rw [bottom_boundary_vertex_laplacian_eq_increment_divergence n hn k]
  change
    (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .west)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .north))) +
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .west)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .north))) +
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .north)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .west))) = _
  rw [fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
        n hn eN heN .west,
      fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
        n hn eN heN .north,
      htNW, htNN]
  rw [<- heE, <- heW]
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [<- fkIsingSquareBottomBoundaryMedialObservable_projection_west
        n hn k1,
      <- fkIsingSquareBottomBoundaryMedialObservable_projection_north
        n hn k1,
      <- fkIsingSquareBottomBoundaryMedialObservable_projection_north
        n hn k0,
      <- fkIsingSquareBottomBoundaryMedialObservable_projection_west
        n hn k0]
  change
    (Complex.normSq (isingProj 1 FE) -
        Complex.normSq (isingProj (-Complex.I) FE)) +
      (Complex.normSq (isingProj (-Complex.I) FN) -
        Complex.normSq (isingProj (-1) FN)) +
      (Complex.normSq (isingProj (-Complex.I) FW) -
        Complex.normSq (isingProj 1 FW)) = _
  rw [hwestRewrite]
  unfold isingPrimalProjectionDivergenceWithoutSouth
  ring


theorem right_boundary_transverse_increment_eq
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.right, k1)
    let hx : fkIsingSquareDirectionAvailable n x .west := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    let e := fkIsingSquareDirectionEdge n x .west hx
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.right, k1)
  let hx : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let e := fkIsingSquareDirectionEdge n x .west hx
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
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
      (fkIsingSquarePerimeterEdge n .right k0, .north) := by
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn dE.1 dE.2]
    change fkIsingSquareBondMate n hn
      (fkIsingSquareDirectionDart n x .west hx .counterclockwise) = _
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir : fkIsingSquareNextDirection n x .west = .south := by
      simp [fkIsingSquareNextDirection, hsouth]
    calc
      _ = fkIsingSquareDirectionDart n x .south hsouth .clockwise :=
        fkIsingSquareDirectionDart_congr n x hdir _ _ _
      _ = (fkIsingSquarePerimeterEdge n .right k0, .north) := by
        apply fkIsingSquareDart_key_injective n
        have htargetEndpoint :
            fkIsingSquareDartEndpoint n
                (fkIsingSquarePerimeterEdge n .right k0, .north) = x := by
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
                (fkIsingSquarePerimeterEdge n .right k0, .north) = .south := by
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
      (fkIsingSquarePerimeterEdge n .right k1, .west) := by
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn dN.1 dN.2]
    change fkIsingSquareBondMate n hn
      (fkIsingSquareDirectionDart n x .west hx .clockwise) = _
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir : fkIsingSquarePreviousDirection n x .west = .north := by
      simp [fkIsingSquarePreviousDirection, hnorth]
    calc
      _ = fkIsingSquareDirectionDart n x .north hnorth .counterclockwise :=
        fkIsingSquareDirectionDart_congr n x hdir _ _ _
      _ = (fkIsingSquarePerimeterEdge n .right k1, .west) := rfl
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
      n hn .right k0
  have hnext := fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    n hn .right k1
  let dC : FKIsingMedialDart (fkSquareBoxPlanar n) :=
    (fkIsingSquarePerimeterEdge n .right k0, .east)
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
      (fkIsingSquarePerimeterEdge n .right k1, .south) := by
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
    have hdirection : fkIsingSquareDartDirection n dC = .south := by
      simp [dC, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
    have hdCrepr : dC =
        fkIsingSquareDirectionDart n x .south hsouth .counterclockwise := by
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
    have hdir : fkIsingSquareNextDirection n x .south = .north := by
      simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable,
        x, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      omega
    calc
      _ = fkIsingSquareDirectionDart n x .north hnorth .clockwise :=
        fkIsingSquareDirectionDart_congr n x hdir _ _ _
      _ = (fkIsingSquarePerimeterEdge n .right k1, .south) := rfl
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
