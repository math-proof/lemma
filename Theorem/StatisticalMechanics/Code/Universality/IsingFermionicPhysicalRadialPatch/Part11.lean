/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part11


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

theorem fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_eq_divergence
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    fkIsingSquareRadialPatchDiagonalLaplacian
        (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j =
      fkIsingSquareRadialPatchPrimalIncrementDivergence
        n m hn hm hmpos i j := by
  have hoddNE : ¬ Even (i + 1 + j) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hoddNW : ¬ Even (i + (j - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hoddSW : ¬ Even (i - 1 + j) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hevenSW : Even (i - 1 + (j - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hevenSE : Even (i - 1 + (j + 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hrE := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos i j (by omega) (by omega)
  have hvE := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos (i + 1) j
  have hvN := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i (j - 1)
  have hrN := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos i (j - 1) (by omega) (by omega)
  have hrW := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos (i - 1) j (by omega) (by omega)
  have hvW := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos (i - 1) (j - 1)
  have hvS := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i j
  have hrS := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos (i - 1) (j + 1) (by omega) (by omega)
  simp only [fkIsingSquareRadialPatchHorizontalSignedIncrement,
    fkIsingSquareRadialPatchVerticalSignedIncrement, heven, hoddNE,
    hoddNW, hoddSW, hevenSW, hevenSE, if_true, if_false] at hrE hvE hvN hrN hrW hvW hvS hrS
  have hiSub : i - 1 + 1 = i := by omega
  have hjSub : j - 1 + 1 = j := by omega
  rw [hiSub] at hrW hrS
  rw [hjSub] at hvN hvW
  unfold fkIsingSquareRadialPatchDiagonalLaplacian
  unfold fkIsingSquareRadialPatchPrimalIncrementDivergence
  dsimp only
  linarith


theorem fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_eq_neg_divergence_of_odd
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (hodd : ¬ Even (i + j)) :
    fkIsingSquareRadialPatchDiagonalLaplacian
        (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j =
      -fkIsingSquareRadialPatchPrimalIncrementDivergence
        n m hn hm hmpos i j := by
  have hevenNE : Even (i + 1 + j) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hevenNW : Even (i + (j - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hevenSW : Even (i - 1 + j) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hoddSW : ¬ Even (i - 1 + (j - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hoddSE : ¬ Even (i - 1 + (j + 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hrE := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos i j (by omega) (by omega)
  have hvE := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos (i + 1) j
  have hvN := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i (j - 1)
  have hrN := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos i (j - 1) (by omega) (by omega)
  have hrW := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos (i - 1) j (by omega) (by omega)
  have hvW := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos (i - 1) (j - 1)
  have hvS := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i j
  have hrS := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos (i - 1) (j + 1) (by omega) (by omega)
  simp only [fkIsingSquareRadialPatchHorizontalSignedIncrement,
    fkIsingSquareRadialPatchVerticalSignedIncrement, hodd, hevenNE,
    hevenNW, hevenSW, hoddSW, hoddSE, if_true, if_false]
    at hrE hvE hvN hrN hrW hvW hvS hrS
  have hiSub : i - 1 + 1 = i := by omega
  have hjSub : j - 1 + 1 = j := by omega
  rw [hiSub] at hrW hrS
  rw [hjSub] at hvN hvW
  unfold fkIsingSquareRadialPatchDiagonalLaplacian
  unfold fkIsingSquareRadialPatchPrimalIncrementDivergence
  dsimp only
  linarith


theorem fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_projectionDivergence
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    fkIsingSquareRadialPatchPrimalIncrementDivergence
        n m hn hm hmpos i j =
      isingPrimalProjectionDivergence
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j - 1, by omega⟩)
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j, by omega⟩)
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i - 1, by omega⟩ ⟨j, by omega⟩)
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩) := by
  have hoddN : ¬ Even (i + (j - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hoddS : ¬ Even (i - 1 + j) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hevenW : Even (i - 1 + (j - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  let eN := fkIsingSquareRadialPatchEdge n m hm
    ⟨i, by omega⟩ ⟨j - 1, by omega⟩
  let eE := fkIsingSquareRadialPatchEdge n m hm
    ⟨i, by omega⟩ ⟨j, by omega⟩
  let eS := fkIsingSquareRadialPatchEdge n m hm
    ⟨i - 1, by omega⟩ ⟨j, by omega⟩
  let eW := fkIsingSquareRadialPatchEdge n m hm
    ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .vertical := by
    rw [show eN = fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hoddN,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisE : (fkIsingSquareOrientedEdge n eE).axis = .horizontal := by
    rw [show eE = fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ heven,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .vertical := by
    rw [show eS = fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hoddS,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .horizontal := by
    rw [show eW = fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ hevenW,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eN haxisN with
    ⟨hNW, hNE, hNS, hNN⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eE haxisE with
    ⟨hEW, hEE, hES, hEN⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eS haxisS with
    ⟨hSW, hSE, hSS, hSN⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eW haxisW with
    ⟨hWW, hWE, hWS, hWN⟩
  let inc := fkIsingSquareInteriorRadialIncrement n hn
  have hEWedge := congrArg inc
    (fkIsingSquareRadialPatchHorizontalIncidence_bottom
      n m hn hm hmpos i j (by omega) (by omega))
  have hENedge := congrArg inc
    (fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
      n m hn hm hmpos i j (by omega) (by omega))
  have hNWedge := congrArg inc
    (fkIsingSquareRadialPatchVerticalIncidence_left
      n m hn hm hmpos i (j - 1) (by omega) (by omega))
  have hNNedge := congrArg inc
    (fkIsingSquareRadialPatchHorizontalIncidence_bottom
      n m hn hm hmpos i (j - 1) (by omega) (by omega))
  have hWEedge := congrArg inc
    (fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
      n m hn hm hmpos (i - 1) (j - 1) (by omega) (by omega))
  have hWSedge := congrArg inc
    (fkIsingSquareRadialPatchVerticalIncidence_left
      n m hn hm hmpos (i - 1) (j - 1) (by omega) (by omega))
  have hSEedge := congrArg inc
    (fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
      n m hn hm hmpos (i - 1) j (by omega) (by omega))
  have hSSedge := congrArg inc
    (fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
      n m hn hm hmpos (i - 1) j (by omega) (by omega))
  simp only [fkIsingSquareRadialPatchBottomSide,
    fkIsingSquareRadialPatchTopSide, fkIsingSquareRadialPatchLeftSide,
    fkIsingSquareRadialPatchRightSide, heven, hoddN, hoddS, hevenW,
    if_true, if_false] at hEWedge hENedge hNWedge hNNedge hWEedge hWSedge hSEedge hSSedge
  have hiSub : i - 1 + 1 = i := by omega
  have hjSub : j - 1 + 1 = j := by omega
  rw [hjSub] at hWEedge
  rw [hiSub] at hSEedge
  dsimp only [inc] at hEWedge hENedge hNWedge hNNedge hWEedge hWSedge hSEedge hSSedge
  unfold fkIsingSquareRadialPatchPrimalIncrementDivergence
  dsimp only
  rw [hEWedge, hENedge, hNWedge, hNNedge, hWEedge, hWSedge,
    hSEedge, hSSedge]
  simp_rw [fkIsingSquareRadialPatchIncidence_increment_eq_normSq_full_projection]
  unfold isingPrimalProjectionDivergence
  unfold fkIsingSquareRadialPatchFullObservable
  rw [hNW, hNN, hEW, hEN, hSE, hSS, hWE, hWS]
  ring


theorem fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_rotated_projectionDivergence_of_odd
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (hodd : ¬ Even (i + j)) :
    fkIsingSquareRadialPatchPrimalIncrementDivergence
        n m hn hm hmpos i j =
      isingPrimalProjectionDivergence
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i - 1, by omega⟩ ⟨j, by omega⟩)
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩)
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j - 1, by omega⟩)
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j, by omega⟩) := by
  have hevenN : Even (i + (j - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hevenS : Even (i - 1 + j) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hoddW : ¬ Even (i - 1 + (j - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  let eN := fkIsingSquareRadialPatchEdge n m hm
    ⟨i, by omega⟩ ⟨j - 1, by omega⟩
  let eE := fkIsingSquareRadialPatchEdge n m hm
    ⟨i, by omega⟩ ⟨j, by omega⟩
  let eS := fkIsingSquareRadialPatchEdge n m hm
    ⟨i - 1, by omega⟩ ⟨j, by omega⟩
  let eW := fkIsingSquareRadialPatchEdge n m hm
    ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .horizontal := by
    rw [show eN = fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ hevenN,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisE : (fkIsingSquareOrientedEdge n eE).axis = .vertical := by
    rw [show eE = fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hodd,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .horizontal := by
    rw [show eS = fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ hevenS,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .vertical := by
    rw [show eW = fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ from rfl,
      fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hoddW,
      fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eN haxisN with
    ⟨hNW, hNE, hNS, hNN⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eE haxisE with
    ⟨hEW, hEE, hES, hEN⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eS haxisS with
    ⟨hSW, hSE, hSS, hSN⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eW haxisW with
    ⟨hWW, hWE, hWS, hWN⟩
  let inc := fkIsingSquareInteriorRadialIncrement n hn
  have hEWedge := congrArg inc
    (fkIsingSquareRadialPatchHorizontalIncidence_bottom
      n m hn hm hmpos i j (by omega) (by omega))
  have hENedge := congrArg inc
    (fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
      n m hn hm hmpos i j (by omega) (by omega))
  have hNWedge := congrArg inc
    (fkIsingSquareRadialPatchVerticalIncidence_left
      n m hn hm hmpos i (j - 1) (by omega) (by omega))
  have hNNedge := congrArg inc
    (fkIsingSquareRadialPatchHorizontalIncidence_bottom
      n m hn hm hmpos i (j - 1) (by omega) (by omega))
  have hWEedge := congrArg inc
    (fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
      n m hn hm hmpos (i - 1) (j - 1) (by omega) (by omega))
  have hWSedge := congrArg inc
    (fkIsingSquareRadialPatchVerticalIncidence_left
      n m hn hm hmpos (i - 1) (j - 1) (by omega) (by omega))
  have hSEedge := congrArg inc
    (fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
      n m hn hm hmpos (i - 1) j (by omega) (by omega))
  have hSSedge := congrArg inc
    (fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
      n m hn hm hmpos (i - 1) j (by omega) (by omega))
  simp only [fkIsingSquareRadialPatchBottomSide,
    fkIsingSquareRadialPatchTopSide, fkIsingSquareRadialPatchLeftSide,
    fkIsingSquareRadialPatchRightSide, hodd, hevenN, hevenS, hoddW,
    if_true, if_false] at hEWedge hENedge hNWedge hNNedge hWEedge hWSedge hSEedge hSSedge
  have hiSub : i - 1 + 1 = i := by omega
  have hjSub : j - 1 + 1 = j := by omega
  rw [hjSub] at hWEedge
  rw [hiSub] at hSEedge
  dsimp only [inc] at hEWedge hENedge hNWedge hNNedge hWEedge hWSedge hSEedge hSSedge
  unfold fkIsingSquareRadialPatchPrimalIncrementDivergence
  dsimp only
  rw [hEWedge, hENedge, hNWedge, hNNedge, hWEedge, hWSedge,
    hSEedge, hSSedge]
  simp_rw [fkIsingSquareRadialPatchIncidence_increment_eq_normSq_full_projection]
  unfold isingPrimalProjectionDivergence
  unfold fkIsingSquareRadialPatchFullObservable
  rw [hEN, hEE, hNS, hNW, hWS, hWW, hSN, hSE]
  ring


theorem fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_primitiveLaplacian
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    fkIsingSquareRadialPatchPrimalIncrementDivergence
        n m hn hm hmpos i j =
      isingPrimalPrimitiveLaplacian
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j - 1, by omega⟩)
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j, by omega⟩)
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i - 1, by omega⟩ ⟨j, by omega⟩)
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩) := by
  rw [fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_projectionDivergence
      n m i j hn hm hmpos hi0 hi1 hj0 hj1 heven]
  exact (isingPrimalPrimitiveLaplacian_eq_projectionDivergence _ _ _ _).symm


theorem fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_nonneg_of_odd
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (hodd : ¬ Even (i + j)) :
    0 ≤ fkIsingSquareRadialPatchDiagonalLaplacian
      (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j := by
  rw [fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_eq_neg_divergence_of_odd
      n m i j hn hm hmpos hi0 hi1 hj0 hj1 hodd,
    fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_rotated_projectionDivergence_of_odd
      n m i j hn hm hmpos hi0 hi1 hj0 hj1 hodd,
    ← isingPrimalPrimitiveLaplacian_eq_projectionDivergence,
    ← isingPrimalPrimitiveLaplacian_rotate_two]
  exact isingPrimalPrimitiveLaplacian_nonneg _ _ _ _
    (fkIsingSquareRadialPatchFullObservable_quad_of_odd
      n m i j hn hm hi0 hi1 hj0 hj1 hodd)


theorem fkIsingSquareRadialPatch_finiteGraphLaplacian_eq_diagonal
    (n m i j : Nat) (hm : m ≤ n)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m)
    (heven : Even (i + j))
    (f : (fkSquareBoxPlanar n).V → Real) (H : Nat → Nat → Real)
    (hc : f (fkIsingSquareRadialPatchVertex n m hm
        ⟨i, by omega⟩ ⟨j, by omega⟩) = H i j)
    (hne : f (fkIsingSquareRadialPatchVertex n m hm
        ⟨i + 1, hi1⟩ ⟨j + 1, hj1⟩) = H (i + 1) (j + 1))
    (hnw : f (fkIsingSquareRadialPatchVertex n m hm
        ⟨i + 1, hi1⟩ ⟨j - 1, by omega⟩) = H (i + 1) (j - 1))
    (hsw : f (fkIsingSquareRadialPatchVertex n m hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩) = H (i - 1) (j - 1))
    (hse : f (fkIsingSquareRadialPatchVertex n m hm
        ⟨i - 1, by omega⟩ ⟨j + 1, hj1⟩) = H (i - 1) (j + 1)) :
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G f
        (fkIsingSquareRadialPatchVertex n m hm
          ⟨i, by omega⟩ ⟨j, by omega⟩) =
      fkIsingSquareRadialPatchDiagonalLaplacian H i j := by
  let pNE : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i + 1, hi1⟩, ⟨j + 1, hj1⟩), by
      change Even ((i + 1) + (j + 1))
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp heven
      omega⟩
  let pNW : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i + 1, hi1⟩, ⟨j - 1, by omega⟩), by
      change Even ((i + 1) + (j - 1))
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp heven
      omega⟩
  let pSW : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i - 1, by omega⟩, ⟨j - 1, by omega⟩), by
      change Even ((i - 1) + (j - 1))
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp heven
      omega⟩
  let pSE : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i - 1, by omega⟩, ⟨j + 1, hj1⟩), by
      change Even ((i - 1) + (j + 1))
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp heven
      omega⟩
  let ne := fkIsingSquareRadialPatchPrimalNodeVertex n m hm pNE
  let nw := fkIsingSquareRadialPatchPrimalNodeVertex n m hm pNW
  let sw := fkIsingSquareRadialPatchPrimalNodeVertex n m hm pSW
  let se := fkIsingSquareRadialPatchPrimalNodeVertex n m hm pSE
  let c := fkIsingSquareRadialPatchVertex n m hm
    ⟨i, by omega⟩ ⟨j, by omega⟩
  have hneighbors : (fkSquareBoxPlanar n).G.neighborFinset c =
      {ne, nw, sw, se} := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton]
    simpa only [c, ne, nw, sw, se, pNE, pNW, pSW, pSE,
      fkIsingSquareRadialPatchPrimalNodeVertex] using
      fkIsingSquareRadialPatch_adj_iff_diagonal
        n m i j hm hi0 hi1 hj0 hj1 heven y
  have hinj := fkIsingSquareRadialPatchPrimalNodeVertex_injective n m hm
  have hpNE_NW : pNE ≠ pNW := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m =>
      p.1.2.1) h
    simp [pNE, pNW] at hk
    omega
  have hpNE_SW : pNE ≠ pSW := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m =>
      p.1.1.1) h
    simp [pNE, pSW] at hk
    omega
  have hpNE_SE : pNE ≠ pSE := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m =>
      p.1.1.1) h
    simp [pNE, pSE] at hk
    omega
  have hpNW_SW : pNW ≠ pSW := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m =>
      p.1.1.1) h
    simp [pNW, pSW] at hk
    omega
  have hpNW_SE : pNW ≠ pSE := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m =>
      p.1.1.1) h
    simp [pNW, pSE] at hk
    omega
  have hpSW_SE : pSW ≠ pSE := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m =>
      p.1.2.1) h
    simp [pSW, pSE] at hk
  have hNE_NW : ne ≠ nw := hinj.ne hpNE_NW
  have hNE_SW : ne ≠ sw := hinj.ne hpNE_SW
  have hNE_SE : ne ≠ se := hinj.ne hpNE_SE
  have hNW_SW : nw ≠ sw := hinj.ne hpNW_SW
  have hNW_SE : nw ≠ se := hinj.ne hpNW_SE
  have hSW_SE : sw ≠ se := hinj.ne hpSW_SE
  unfold isingFiniteGraphLaplacian
  rw [hneighbors]
  simp [hNE_NW, hNE_SW, hNE_SE, hNW_SW, hNW_SE, hSW_SE]
  simp only [c, ne, nw, sw, se, pNE, pNW, pSW, pSE,
    fkIsingSquareRadialPatchPrimalNodeVertex] at hc hne hnw hsw hse ⊢
  rw [hc, hne, hnw, hsw, hse]
  unfold fkIsingSquareRadialPatchDiagonalLaplacian
  ring


end
end StatMech.Universality
