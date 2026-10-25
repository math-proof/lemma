/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part26
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWindowRealization.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryRadialPatchFullValue_horizontal_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m) :
    fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
          ⟨i + 1, hi⟩ ⟨j, hj⟩ -
        fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
          ⟨i, by omega⟩ ⟨j, hj⟩ =
      fkIsingSquareBoundaryRadialPatchHorizontalSignedIncrement
        n m hn hm (by omega) i j := by
  let e := fkIsingSquareRadialPatchHorizontalIncidence
    n m hn hm (by omega) i j
  have hc := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex
    n hn e
  by_cases heven : Even (i + j)
  · have hnext : ¬ Even ((i + 1) + j) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    rw [fkIsingSquareRadialPatchHorizontal_face_of_even
        n m hn hm (by omega) i j hi hj heven,
      fkIsingSquareRadialPatchHorizontal_endpoint_of_even
        n m hn hm (by omega) i j hi hj heven] at hc
    simpa [fkIsingSquareBoundaryRadialPatchFullValue,
      fkIsingSquareRadialPatchFullValue,
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue,
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue,
      fkIsingSquareBoundaryRadialPatchHorizontalSignedIncrement,
      heven, hnext, e] using hc
  · have hnext : Even ((i + 1) + j) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    rw [fkIsingSquareRadialPatchHorizontal_face_of_odd
        n m hn hm (by omega) i j hi hj heven,
      fkIsingSquareRadialPatchHorizontal_endpoint_of_odd
        n m hn hm (by omega) i j hi hj heven] at hc
    simp only [fkIsingSquareBoundaryRadialPatchFullValue,
      fkIsingSquareRadialPatchFullValue, hnext, heven,
      dite_true, dite_false,
      fkIsingSquareBoundaryRadialPatchHorizontalSignedIncrement, if_false]
    change _ = -fkIsingSquareBoundaryLayerRadialIncrement n hn e
    linarith

theorem fkIsingSquareBoundaryRadialPatchFullValue_vertical_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m) :
    fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
          ⟨i, hi⟩ ⟨j + 1, hj⟩ -
        fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
          ⟨i, hi⟩ ⟨j, by omega⟩ =
      fkIsingSquareBoundaryRadialPatchVerticalSignedIncrement
        n m hn hm (by omega) i j := by
  let e := fkIsingSquareRadialPatchVerticalIncidence
    n m hn hm (by omega) i j
  have hc := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex
    n hn e
  by_cases heven : Even (i + j)
  · have hnext : ¬ Even (i + (j + 1)) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    rw [fkIsingSquareRadialPatchVertical_face_of_even
        n m hn hm (by omega) i j hi hj heven,
      fkIsingSquareRadialPatchVertical_endpoint_of_even
        n m hn hm (by omega) i j hi hj heven] at hc
    simpa [fkIsingSquareBoundaryRadialPatchFullValue,
      fkIsingSquareRadialPatchFullValue,
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue,
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue,
      fkIsingSquareBoundaryRadialPatchVerticalSignedIncrement,
      heven, hnext, e] using hc
  · have hnext : Even (i + (j + 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    rw [fkIsingSquareRadialPatchVertical_face_of_odd
        n m hn hm (by omega) i j hi hj heven,
      fkIsingSquareRadialPatchVertical_endpoint_of_odd
        n m hn hm (by omega) i j hi hj heven] at hc
    simp only [fkIsingSquareBoundaryRadialPatchFullValue,
      fkIsingSquareRadialPatchFullValue, hnext, heven,
      dite_true, dite_false,
      fkIsingSquareBoundaryRadialPatchVerticalSignedIncrement, if_false]
    change _ = -fkIsingSquareBoundaryLayerRadialIncrement n hn e
    linarith


theorem fkIsingSquareBoundaryRadialPatch_normSq_full_le_diagonalVariation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (i j : Nat) (hi : i + 1 < m) (hj : j + 1 < m) :
    Complex.normSq
        (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j, by omega⟩) ≤
      2 *
        (|fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
              ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ -
            fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
              ⟨i, by omega⟩ ⟨j, by omega⟩| +
          |fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
              ⟨i + 1, hi⟩ ⟨j, by omega⟩ -
            fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
              ⟨i, by omega⟩ ⟨j + 1, hj⟩|) := by
  let ii : Fin m := ⟨i, by omega⟩
  let jj : Fin m := ⟨j, by omega⟩
  let F := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ii jj
  let e := fkIsingSquareRadialPatchEdge n m hm ii jj
  let H := fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
  have hbottom := fkIsingSquareBoundaryRadialPatchFullValue_horizontal_increment
    n m hn hm hm2 i j hi (by omega)
  have htop := fkIsingSquareBoundaryRadialPatchFullValue_horizontal_increment
    n m hn hm hm2 i (j + 1) hi hj
  have hleft := fkIsingSquareBoundaryRadialPatchFullValue_vertical_increment
    n m hn hm hm2 i j (by omega) hj
  have hright := fkIsingSquareBoundaryRadialPatchFullValue_vertical_increment
    n m hn hm hm2 (i + 1) j hi hj
  have hinc (s : FKIsingMedialSide) :=
    fkIsingSquareBoundaryRadialPatchIncidence_increment_eq_normSq_projection
      n m hn hm ii jj s
  by_cases heven : Even (i + j)
  · have htopOdd : ¬ Even (i + (j + 1)) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    have hrightOdd : ¬ Even (i + 1 + j) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal := by
      dsimp [e, ii, jj]
      rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ heven,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
      ⟨hW, hE, hS, hN⟩
    simp only [fkIsingSquareBoundaryRadialPatchHorizontalSignedIncrement,
      fkIsingSquareBoundaryRadialPatchVerticalSignedIncrement,
      heven, htopOdd, hrightOdd, if_true, if_false] at hbottom htop hleft hright
    rw [fkIsingSquareRadialPatchHorizontalIncidence_bottom
        n m hn hm (by omega) i j (by omega) (by omega)] at hbottom
    rw [fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
        n m hn hm (by omega) i j (by omega) (by omega)] at htop
    rw [fkIsingSquareRadialPatchVerticalIncidence_left
        n m hn hm (by omega) i j (by omega) (by omega)] at hleft
    rw [fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
        n m hn hm (by omega) i j (by omega) (by omega)] at hright
    simp only [fkIsingSquareRadialPatchBottomSide,
      fkIsingSquareRadialPatchTopSide, fkIsingSquareRadialPatchLeftSide,
      fkIsingSquareRadialPatchRightSide, heven, if_true] at hbottom htop hleft hright
    have hdiagPrimal : H ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ -
          H ⟨i, by omega⟩ ⟨j, by omega⟩ =
        Complex.normSq (isingProj Complex.I F) -
          Complex.normSq (isingProj (-1) F) := by
      dsimp [H, F, e, ii, jj] at hW hE hS hN ⊢
      calc
        _ = (fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                ⟨i, by omega⟩ ⟨j + 1, hj⟩ -
              fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                ⟨i, by omega⟩ ⟨j, by omega⟩) +
            (fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ -
              fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                ⟨i, by omega⟩ ⟨j + 1, hj⟩) := by ring
        _ = fkIsingSquareBoundaryLayerRadialIncrement n hn
              (fkIsingSquareRadialPatchIncidence n m hn hm ii jj .south) -
            fkIsingSquareBoundaryLayerRadialIncrement n hn
              (fkIsingSquareRadialPatchIncidence n m hn hm ii jj .east) := by
                rw [hleft, htop]
                ring
        _ = _ := by
          rw [hinc .south, hinc .east, hS, hE]
    have hdiagDual : H ⟨i + 1, hi⟩ ⟨j, by omega⟩ -
          H ⟨i, by omega⟩ ⟨j + 1, hj⟩ =
        Complex.normSq (isingProj 1 F) -
          Complex.normSq (isingProj Complex.I F) := by
      dsimp [H, F, e, ii, jj] at hW hE hS hN ⊢
      calc
        _ = (fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                ⟨i + 1, hi⟩ ⟨j, by omega⟩ -
              fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                ⟨i, by omega⟩ ⟨j, by omega⟩) -
            (fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                ⟨i, by omega⟩ ⟨j + 1, hj⟩ -
              fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                ⟨i, by omega⟩ ⟨j, by omega⟩) := by ring
        _ = fkIsingSquareBoundaryLayerRadialIncrement n hn
              (fkIsingSquareRadialPatchIncidence n m hn hm ii jj .west) -
            fkIsingSquareBoundaryLayerRadialIncrement n hn
              (fkIsingSquareRadialPatchIncidence n m hn hm ii jj .south) := by
                rw [hbottom, hleft]
        _ = _ := by
          rw [hinc .west, hinc .south, hW, hS]
    dsimp [F, H, ii, jj] at hdiagPrimal hdiagDual ⊢
    rw [hdiagPrimal, hdiagDual]
    exact isingProj_normSq_le_two_mul_diagonal_variation _

  · have htopEven : Even (i + (j + 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    have hrightEven : Even (i + 1 + j) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical := by
      dsimp [e, ii, jj]
      rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ heven,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
      ⟨hW, hE, hS, hN⟩
    simp only [fkIsingSquareBoundaryRadialPatchHorizontalSignedIncrement,
      fkIsingSquareBoundaryRadialPatchVerticalSignedIncrement,
      heven, htopEven, hrightEven, if_true, if_false] at hbottom htop hleft hright
    rw [fkIsingSquareRadialPatchHorizontalIncidence_bottom
        n m hn hm (by omega) i j (by omega) (by omega)] at hbottom
    rw [fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
        n m hn hm (by omega) i j (by omega) (by omega)] at htop
    rw [fkIsingSquareRadialPatchVerticalIncidence_left
        n m hn hm (by omega) i j (by omega) (by omega)] at hleft
    rw [fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
        n m hn hm (by omega) i j (by omega) (by omega)] at hright
    simp only [fkIsingSquareRadialPatchBottomSide,
      fkIsingSquareRadialPatchTopSide, fkIsingSquareRadialPatchLeftSide,
      fkIsingSquareRadialPatchRightSide, heven, if_false] at hbottom htop hleft hright
    have hclosed := isingPrimitiveIncrement_local_closed 1 Complex.I F
      (by norm_num) (by norm_num)
    unfold isingPrimitiveIncrement at hclosed
    have hdiagPrimal : H ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ -
          H ⟨i, by omega⟩ ⟨j, by omega⟩ =
        Complex.normSq (isingProj Complex.I F) -
          Complex.normSq (isingProj (-1) F) := by
      have hraw : H ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ -
            H ⟨i, by omega⟩ ⟨j, by omega⟩ =
          Complex.normSq (isingProj 1 F) -
            Complex.normSq (isingProj (-Complex.I) F) := by
        dsimp [H, F, e, ii, jj] at hW hE hS hN ⊢
        calc
          _ = (fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                  ⟨i, by omega⟩ ⟨j + 1, hj⟩ -
                fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                  ⟨i, by omega⟩ ⟨j, by omega⟩) +
              (fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                  ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ -
                fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                  ⟨i, by omega⟩ ⟨j + 1, hj⟩) := by ring
          _ = -fkIsingSquareBoundaryLayerRadialIncrement n hn
                (fkIsingSquareRadialPatchIncidence n m hn hm ii jj .west) +
              fkIsingSquareBoundaryLayerRadialIncrement n hn
                (fkIsingSquareRadialPatchIncidence n m hn hm ii jj .south) := by
                  rw [hleft, htop]
          _ = _ := by
            rw [hinc .west, hinc .south, hW, hS]
            ring
      linarith
    have hdiagDual : H ⟨i + 1, hi⟩ ⟨j, by omega⟩ -
          H ⟨i, by omega⟩ ⟨j + 1, hj⟩ =
        Complex.normSq (isingProj 1 F) -
          Complex.normSq (isingProj Complex.I F) := by
      have hraw : H ⟨i + 1, hi⟩ ⟨j, by omega⟩ -
            H ⟨i, by omega⟩ ⟨j + 1, hj⟩ =
          Complex.normSq (isingProj (-Complex.I) F) -
            Complex.normSq (isingProj (-1) F) := by
        dsimp [H, F, e, ii, jj] at hW hE hS hN ⊢
        calc
          _ = (fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                  ⟨i + 1, hi⟩ ⟨j, by omega⟩ -
                fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                  ⟨i, by omega⟩ ⟨j, by omega⟩) -
              (fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                  ⟨i, by omega⟩ ⟨j + 1, hj⟩ -
                fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                  ⟨i, by omega⟩ ⟨j, by omega⟩) := by ring
          _ = -fkIsingSquareBoundaryLayerRadialIncrement n hn
                (fkIsingSquareRadialPatchIncidence n m hn hm ii jj .north) +
              fkIsingSquareBoundaryLayerRadialIncrement n hn
                (fkIsingSquareRadialPatchIncidence n m hn hm ii jj .west) := by
                  rw [hbottom, hleft]
                  ring
          _ = _ := by
            rw [hinc .north, hinc .west, hN, hW]
            ring
      linarith
    dsimp [F, H, ii, jj] at hdiagPrimal hdiagDual ⊢
    rw [hdiagPrimal, hdiagDual]
    exact isingProj_normSq_le_two_mul_diagonal_variation _


end
end StatMech.Universality
