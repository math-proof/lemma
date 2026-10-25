/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part6


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

theorem fkIsingSquareRadialPatchFullObservable_projection
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Fin m) (s : FKIsingMedialSide) :
    isingProj
        (fkIsingSquareWiredDirectedTangent n hn
          (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)))
        (fkIsingSquareRadialPatchFullObservable n m hn hm i j) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)) := by
  exact fkIsingSquareWiredFullMedialObservable_projection n hn _ s


theorem fkIsingSquareRadialPatch_normSq_full_eq_bottom_add_top_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (i j : Fin m) :
    Complex.normSq
        (fkIsingSquareRadialPatchFullObservable n m hn hm i j) =
      fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareRadialPatchIncidence n m hn hm i j
            (fkIsingSquareRadialPatchBottomSide i j)) +
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareRadialPatchIncidence n m hn hm i j
            (fkIsingSquareRadialPatchTopSide i j)) := by
  by_cases heven : Even (i.1 + j.1)
  · simpa [fkIsingSquareRadialPatchFullObservable,
      fkIsingSquareRadialPatchIncidence,
      fkIsingSquareInteriorRadialCellIncidence,
      fkIsingSquareRadialPatchBottomSide,
      fkIsingSquareRadialPatchTopSide, heven] using
      fkIsingSquareWired_normSq_full_eq_west_add_east_increment n hn
        (fkIsingSquareRadialPatchEdge n m hm i j)
  · simpa [fkIsingSquareRadialPatchFullObservable,
      fkIsingSquareRadialPatchIncidence,
      fkIsingSquareInteriorRadialCellIncidence,
      fkIsingSquareRadialPatchBottomSide,
      fkIsingSquareRadialPatchTopSide, heven, add_comm] using
      fkIsingSquareWired_normSq_full_eq_south_add_north_increment n hn
        (fkIsingSquareRadialPatchEdge n m hm i j)


theorem fkIsingSquareRadialPatch_normSq_full_eq_left_add_right_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (i j : Fin m) :
    Complex.normSq
        (fkIsingSquareRadialPatchFullObservable n m hn hm i j) =
      fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareRadialPatchIncidence n m hn hm i j
            (fkIsingSquareRadialPatchLeftSide i j)) +
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareRadialPatchIncidence n m hn hm i j
            (fkIsingSquareRadialPatchRightSide i j)) := by
  by_cases heven : Even (i.1 + j.1)
  · simpa [fkIsingSquareRadialPatchFullObservable,
      fkIsingSquareRadialPatchIncidence,
      fkIsingSquareInteriorRadialCellIncidence,
      fkIsingSquareRadialPatchLeftSide,
      fkIsingSquareRadialPatchRightSide, heven] using
      fkIsingSquareWired_normSq_full_eq_south_add_north_increment n hn
        (fkIsingSquareRadialPatchEdge n m hm i j)
  · simpa [fkIsingSquareRadialPatchFullObservable,
      fkIsingSquareRadialPatchIncidence,
      fkIsingSquareInteriorRadialCellIncidence,
      fkIsingSquareRadialPatchLeftSide,
      fkIsingSquareRadialPatchRightSide, heven] using
      fkIsingSquareWired_normSq_full_eq_west_add_east_increment n hn
        (fkIsingSquareRadialPatchEdge n m hm i j)


theorem fkIsingSquareRadialPatchIncidence_right_eq_left
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m) :
    fkIsingSquareRadialPatchIncidence n m hn hm
        ⟨i, by omega⟩ ⟨j, hj⟩ (fkIsingSquareRadialPatchRightSide i j) =
      fkIsingSquareRadialPatchIncidence n m hn hm
        ⟨i + 1, hi⟩ ⟨j, hj⟩
        (fkIsingSquareRadialPatchLeftSide (i + 1) j) := by
  let a : Fin m := ⟨i, by omega⟩
  let b : Fin m := ⟨i + 1, hi⟩
  let c : Fin m := ⟨j, hj⟩
  let d : FKIsingSquareInteriorRadialDart n :=
    ⟨(fkIsingSquareRadialPatchEdge n m hm a c,
        fkIsingSquareRadialPatchRightSide i j),
      (fkIsingSquareRadialPatchCell n m hm a c).2 _⟩
  let e : FKIsingSquareInteriorRadialDart n :=
    ⟨(fkIsingSquareRadialPatchEdge n m hm b c,
        fkIsingSquareRadialPatchLeftSide (i + 1) j),
      (fkIsingSquareRadialPatchCell n m hm b c).2 _⟩
  change Quot.mk _ d = Quot.mk _ e
  apply Quot.sound
  have hstep : fkIsingSquareInteriorRadialBondPerm n hn d = e := by
    apply Subtype.ext
    change fkIsingSquareWiredBondMate n hn d.1 = e.1
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d.1 d.2]
    exact fkIsingSquareRadialPatch_bondMate_right n m hn hm i j hi hj
  have hcycle :=
    (Equiv.Perm.SameCycle.rfl :
      (fkIsingSquareInteriorRadialBondPerm n hn).SameCycle d d).apply_right
  simpa only [hstep] using hcycle

theorem fkIsingSquareRadialPatch_bondMate_top
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m) :
    fkIsingSquareBondMate n hn
        (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩,
          fkIsingSquareRadialPatchTopSide i j) =
      (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j + 1, hj⟩,
        fkIsingSquareRadialPatchBottomSide i (j + 1)) := by
  let a : Fin m := ⟨i, hi⟩
  let b : Fin m := ⟨j, by omega⟩
  let c : Fin m := ⟨j + 1, hj⟩
  change fkIsingSquareBondMate n hn
      (fkIsingSquareRadialPatchEdge n m hm a b,
        fkIsingSquareRadialPatchTopSide i j) =
    (fkIsingSquareRadialPatchEdge n m hm a c,
      fkIsingSquareRadialPatchBottomSide i (j + 1))
  have hq : fkIsingSquareRadialPatchHalf i j < n := by
    simpa [a, b] using fkIsingSquareRadialPatchHalf_lt hm a b
  have hq' : fkIsingSquareRadialPatchHalf i (j + 1) < n := by
    simpa [a, c] using fkIsingSquareRadialPatchHalf_lt hm a c
  have hx : (fkIsingSquareRadialPatchHalf i j : Int) < (n : Int) := by
    exact_mod_cast hq
  have hxlow : -(n : Int) < (fkIsingSquareRadialPatchHalf i j : Int) := by
    omega
  have hy : (i : Int) - fkIsingSquareRadialPatchHalf i j < (n : Int) := by
    have hin : i < n := by omega
    omega
  have hylow : -(n : Int) <
      (i : Int) - fkIsingSquareRadialPatchHalf i j := by omega
  have hx' : (fkIsingSquareRadialPatchHalf i (j + 1) : Int) < (n : Int) := by
    exact_mod_cast hq'
  have hxlow' : -(n : Int) <
      (fkIsingSquareRadialPatchHalf i (j + 1) : Int) := by omega
  have hy' : (i : Int) - fkIsingSquareRadialPatchHalf i (j + 1) <
      (n : Int) := by
    have hin : i < n := by omega
    omega
  have hylow' : -(n : Int) <
      (i : Int) - fkIsingSquareRadialPatchHalf i (j + 1) := by omega
  by_cases heven : Even (i + j)
  · have hnext : ¬ Even (i + (j + 1)) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    have hhalf : fkIsingSquareRadialPatchHalf i (j + 1) =
        fkIsingSquareRadialPatchHalf i j + 1 := by
      have hmod := Nat.even_iff.mp heven
      unfold fkIsingSquareRadialPatchHalf
      omega
    rw [fkIsingSquareRadialPatchEdge_eq_east n m hm a b
        (by simpa [a, b] using heven),
      fkIsingSquareRadialPatchEdge_eq_north n m hm a c
        (by simpa [a, c, Nat.add_assoc] using hnext)]
    rw [show fkIsingSquareRadialPatchTopSide i j = .east by
      simp [fkIsingSquareRadialPatchTopSide, heven]]
    rw [show fkIsingSquareRadialPatchBottomSide i (j + 1) = .north by
      simp [fkIsingSquareRadialPatchBottomSide, hnext]]
    apply fkIsingSquareDart_key_injective n
    simp [fkIsingSquareBondMate, fkIsingSquareNextDirection,
      fkIsingSquarePreviousDirection, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, a, b, c,
      fkIsingSquareDirectionDart, fkIsingSquareSideCorner,
      fkIsingSquareCornerSide, fkIsingSquareEndpointForDirection,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, hhalf,
      hx, hxlow, hy, hylow, hx', hxlow', hy', hylow']
    apply Subtype.ext
    funext k
    fin_cases k <;> simp <;> ring
  · have hnext : Even (i + (j + 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    have hhalf : fkIsingSquareRadialPatchHalf i (j + 1) =
        fkIsingSquareRadialPatchHalf i j := by
      have hmod := Nat.not_even_iff.mp heven
      unfold fkIsingSquareRadialPatchHalf
      omega
    rw [fkIsingSquareRadialPatchEdge_eq_north n m hm a b
        (by simpa [a, b] using heven),
      fkIsingSquareRadialPatchEdge_eq_east n m hm a c
        (by simpa [a, c, Nat.add_assoc] using hnext)]
    rw [show fkIsingSquareRadialPatchTopSide i j = .south by
      simp [fkIsingSquareRadialPatchTopSide, heven]]
    rw [show fkIsingSquareRadialPatchBottomSide i (j + 1) = .west by
      simp [fkIsingSquareRadialPatchBottomSide, hnext]]
    apply fkIsingSquareDart_key_injective n
    simp [fkIsingSquareBondMate, fkIsingSquareNextDirection,
      fkIsingSquarePreviousDirection, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, a, b, c,
      fkIsingSquareDirectionDart, fkIsingSquareSideCorner,
      fkIsingSquareCornerSide, fkIsingSquareEndpointForDirection,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, hhalf,
      hx, hxlow, hy, hylow, hx', hxlow', hy', hylow']


theorem fkIsingSquareRadialPatch_directedTangentCode_right_modEq
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m) :
    fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareRadialPatchEdge n m hm ⟨i + 1, hi⟩ ⟨j, hj⟩,
          fkIsingSquareRadialPatchLeftSide (i + 1) j)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩,
          fkIsingSquareRadialPatchRightSide i j)) [ZMOD 8] := by
  by_cases heven : Even (i + j)
  · have hnext : ¬ Even (i + 1 + j) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    have haxisD : (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩)).axis =
        .horizontal := by
      rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ heven,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    have haxisF : (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm ⟨i + 1, hi⟩ ⟨j, hj⟩)).axis =
        .vertical := by
      rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hnext,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    rcases fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
      n hn _ haxisD with ⟨_, _, _, hD⟩
    rcases fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
      n hn _ haxisF with ⟨hF, _, _, _⟩
    simp [fkIsingSquareRadialPatchRightSide, fkIsingSquareRadialPatchLeftSide,
      heven, hnext, hD, hF, Int.ModEq]
  · have hnext : Even (i + 1 + j) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    have haxisD : (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩)).axis =
        .vertical := by
      rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ heven,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    have haxisF : (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm ⟨i + 1, hi⟩ ⟨j, hj⟩)).axis =
        .horizontal := by
      rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ hnext,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    rcases fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
      n hn _ haxisD with ⟨_, hD, _, _⟩
    rcases fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
      n hn _ haxisF with ⟨_, _, hF, _⟩
    simp [fkIsingSquareRadialPatchRightSide, fkIsingSquareRadialPatchLeftSide,
      heven, hnext, hD, hF]


theorem fkIsingSquareRadialPatch_directedTangentCode_top_modEq
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m) :
    fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j + 1, hj⟩,
          fkIsingSquareRadialPatchBottomSide i (j + 1))) ≡
      fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩,
          fkIsingSquareRadialPatchTopSide i j)) [ZMOD 8] := by
  by_cases heven : Even (i + j)
  · have hnext : ¬ Even (i + (j + 1)) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    have haxisD : (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩)).axis =
        .horizontal := by
      rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ heven,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    have haxisF : (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j + 1, hj⟩)).axis =
        .vertical := by
      rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hnext,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    rcases fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
      n hn _ haxisD with ⟨_, hD, _, _⟩
    rcases fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
      n hn _ haxisF with ⟨_, _, _, hF⟩
    simp [fkIsingSquareRadialPatchTopSide, fkIsingSquareRadialPatchBottomSide,
      heven, hnext, hD, hF, Int.ModEq]
  · have hnext : Even (i + (j + 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    have haxisD : (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩)).axis =
        .vertical := by
      rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ heven,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    have haxisF : (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j + 1, hj⟩)).axis =
        .horizontal := by
      rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ hnext,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    rcases fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
      n hn _ haxisD with ⟨_, _, hD, _⟩
    rcases fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
      n hn _ haxisF with ⟨hF, _, _, _⟩
    simp [fkIsingSquareRadialPatchTopSide, fkIsingSquareRadialPatchBottomSide,
      heven, hnext, hD, hF, Int.ModEq]


theorem fkIsingSquareRadialPatch_fermionicObservable_right_eq_left
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩,
          fkIsingSquareRadialPatchRightSide i j)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareRadialPatchEdge n m hm ⟨i + 1, hi⟩ ⟨j, hj⟩,
          fkIsingSquareRadialPatchLeftSide (i + 1) j)) := by
  let a : Fin m := ⟨i, by omega⟩
  let b : Fin m := ⟨i + 1, hi⟩
  let c : Fin m := ⟨j, hj⟩
  let d : FKIsingSquareInteriorRadialDart n :=
    ⟨(fkIsingSquareRadialPatchEdge n m hm a c,
        fkIsingSquareRadialPatchRightSide i j),
      (fkIsingSquareRadialPatchCell n m hm a c).2 _⟩
  have hcode : fkIsingSquareWiredDirectedTangentCode n hn
      (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
    change fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d.1 d.2,
      fkIsingSquareRadialPatch_bondMate_right n m hn hm i j hi hj]
    exact fkIsingSquareRadialPatch_directedTangentCode_right_modEq
      n m hn hm i j hi hj
  have hobs :=
    fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq
      n hn d hcode
  change (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart d.1) at hobs
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d.1 d.2,
    fkIsingSquareRadialPatch_bondMate_right n m hn hm i j hi hj] at hobs
  simpa only [a, b, c, d] using hobs.symm


theorem fkIsingSquareRadialPatch_fermionicObservable_top_eq_bottom
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩,
          fkIsingSquareRadialPatchTopSide i j)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j + 1, hj⟩,
          fkIsingSquareRadialPatchBottomSide i (j + 1))) := by
  let a : Fin m := ⟨i, hi⟩
  let b : Fin m := ⟨j, by omega⟩
  let c : Fin m := ⟨j + 1, hj⟩
  let d : FKIsingSquareInteriorRadialDart n :=
    ⟨(fkIsingSquareRadialPatchEdge n m hm a b,
        fkIsingSquareRadialPatchTopSide i j),
      (fkIsingSquareRadialPatchCell n m hm a b).2 _⟩
  have hcode : fkIsingSquareWiredDirectedTangentCode n hn
      (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
    change fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d.1 d.2,
      fkIsingSquareRadialPatch_bondMate_top n m hn hm i j hi hj]
    exact fkIsingSquareRadialPatch_directedTangentCode_top_modEq
      n m hn hm i j hi hj
  have hobs :=
    fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq
      n hn d hcode
  change (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart d.1) at hobs
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d.1 d.2,
    fkIsingSquareRadialPatch_bondMate_top n m hn hm i j hi hj] at hobs
  simpa only [a, b, c, d] using hobs.symm


theorem fkIsingSquareRadialPatchFullObservable_quad
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩)
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩)
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩)
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j, by omega⟩) := by
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
  have hiSub : i - 1 + 1 = i := by omega
  have hjSub : j - 1 + 1 = j := by omega
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
    simpa only [eN, eE, fkIsingSquareRadialPatchTopSide,
      fkIsingSquareRadialPatchBottomSide, hoddN, heven, if_false, if_true,
      hjSub] using fkIsingSquareRadialPatch_fermionicObservable_top_eq_bottom
        n m hn hm i (j - 1) (by omega) (by omega)
  have hESobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .south)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .east)) := by
    symm
    simpa only [eE, eS, fkIsingSquareRadialPatchRightSide,
      fkIsingSquareRadialPatchLeftSide, hoddS, heven, if_false, if_true,
      hiSub] using fkIsingSquareRadialPatch_fermionicObservable_right_eq_left
        n m hn hm (i - 1) j (by omega) (by omega)
  have hSWobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := by
    symm
    simpa only [eS, eW, fkIsingSquareRadialPatchTopSide,
      fkIsingSquareRadialPatchBottomSide, hevenW, hoddS, if_false, if_true,
      hjSub] using fkIsingSquareRadialPatch_fermionicObservable_top_eq_bottom
        n m hn hm (i - 1) (j - 1) (by omega) (by omega)
  have hWNobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .north)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .west)) := by
    simpa only [eW, eN, fkIsingSquareRadialPatchRightSide,
      fkIsingSquareRadialPatchLeftSide, hevenW, hoddN, if_false, if_true,
      hiSub] using fkIsingSquareRadialPatch_fermionicObservable_right_eq_left
        n m hn hm (i - 1) (j - 1) (by omega) (by omega)
  let north := fkIsingSquareRadialPatchFullObservable n m hn hm
    ⟨i, by omega⟩ ⟨j - 1, by omega⟩
  let east := fkIsingSquareRadialPatchFullObservable n m hn hm
    ⟨i, by omega⟩ ⟨j, by omega⟩
  let south := fkIsingSquareRadialPatchFullObservable n m hn hm
    ⟨i - 1, by omega⟩ ⟨j, by omega⟩
  let west := fkIsingSquareRadialPatchFullObservable n m hn hm
    ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
  change IsingSquareSHolomorphicQuad south west north east
  apply isingSquareSHolomorphicQuad_of_projection_cycle north east south west
  · change isingProj 1 north = isingProj 1 east
    calc
      isingProj 1 north = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .south)))
          north := by rw [hNS]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) := by
        simpa only [north, eN] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i, by omega⟩ ⟨j - 1, by omega⟩ .south
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) := hNEobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eE, .west)))
          east := by
        symm
        simpa only [east, eE] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i, by omega⟩ ⟨j, by omega⟩ .west
      _ = isingProj 1 east := by rw [hEW]
  · change isingProj Complex.I east = isingProj Complex.I south
    calc
      isingProj Complex.I east = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eE, .south)))
          east := by rw [hES]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .south)) := by
        simpa only [east, eE] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i, by omega⟩ ⟨j, by omega⟩ .south
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .east)) := hESobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .east)))
          south := by
        symm
        simpa only [south, eS] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i - 1, by omega⟩ ⟨j, by omega⟩ .east
      _ = isingProj Complex.I south := by rw [hSE]
  · change isingProj (-1) south = isingProj (-1) west
    calc
      isingProj (-1) south = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .north)))
          south := by rw [hSN]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) := by
        simpa only [south, eS] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i - 1, by omega⟩ ⟨j, by omega⟩ .north
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := hSWobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .east)))
          west := by
        symm
        simpa only [west, eW] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ .east
      _ = isingProj (-1) west := by rw [hWE]
  · change isingProj (-Complex.I) west = isingProj (-Complex.I) north
    calc
      isingProj (-Complex.I) west = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .north)))
          west := by rw [hWN]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .north)) := by
        simpa only [west, eW] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ .north
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .west)) := hWNobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .west)))
          north := by
        symm
        simpa only [north, eN] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i, by omega⟩ ⟨j - 1, by omega⟩ .west
      _ = isingProj (-Complex.I) north := by rw [hNW]


theorem fkIsingSquareRadialPatchFullObservable_quad_of_odd
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (hodd : ¬ Even (i + j)) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩)
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j, by omega⟩)
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩)
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩) := by
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
  have hiSub : i - 1 + 1 = i := by omega
  have hjSub : j - 1 + 1 = j := by omega
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
    ⟨_, hNE, hNS, _⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eE haxisE with
    ⟨hEW, _, _, hEN⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eS haxisS with
    ⟨hSW, _, _, hSN⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eW haxisW with
    ⟨_, hWE, hWS, _⟩
  have hNEobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .east)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .north)) := by
    simpa only [eN, eE, fkIsingSquareRadialPatchTopSide,
      fkIsingSquareRadialPatchBottomSide, hevenN, hodd, if_false, if_true,
      hjSub] using fkIsingSquareRadialPatch_fermionicObservable_top_eq_bottom
        n m hn hm i (j - 1) (by omega) (by omega)
  have hESobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) := by
    symm
    simpa only [eE, eS, fkIsingSquareRadialPatchRightSide,
      fkIsingSquareRadialPatchLeftSide, hevenS, hodd, if_false, if_true,
      hiSub] using fkIsingSquareRadialPatch_fermionicObservable_right_eq_left
        n m hn hm (i - 1) j (by omega) (by omega)
  have hSWobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .west)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .south)) := by
    symm
    simpa only [eS, eW, fkIsingSquareRadialPatchTopSide,
      fkIsingSquareRadialPatchBottomSide, hoddW, hevenS, if_false, if_true,
      hjSub] using fkIsingSquareRadialPatch_fermionicObservable_top_eq_bottom
        n m hn hm (i - 1) (j - 1) (by omega) (by omega)
  have hWNobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) := by
    simpa only [eW, eN, fkIsingSquareRadialPatchRightSide,
      fkIsingSquareRadialPatchLeftSide, hoddW, hevenN, if_false, if_true,
      hiSub] using fkIsingSquareRadialPatch_fermionicObservable_right_eq_left
        n m hn hm (i - 1) (j - 1) (by omega) (by omega)
  let north := fkIsingSquareRadialPatchFullObservable n m hn hm
    ⟨i, by omega⟩ ⟨j - 1, by omega⟩
  let east := fkIsingSquareRadialPatchFullObservable n m hn hm
    ⟨i, by omega⟩ ⟨j, by omega⟩
  let south := fkIsingSquareRadialPatchFullObservable n m hn hm
    ⟨i - 1, by omega⟩ ⟨j, by omega⟩
  let west := fkIsingSquareRadialPatchFullObservable n m hn hm
    ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
  change IsingSquareSHolomorphicQuad north east south west
  apply isingSquareSHolomorphicQuad_of_projection_cycle south west north east
  · calc
      isingProj 1 south = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .west)))
          south := by rw [hSW]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .west)) := by
        simpa only [south, eS] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i - 1, by omega⟩ ⟨j, by omega⟩ .west
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .south)) := hSWobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .south)))
          west := by
        symm
        simpa only [west, eW] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ .south
      _ = isingProj 1 west := by rw [hWS]
  · calc
      isingProj Complex.I west = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .east)))
          west := by rw [hWE]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := by
        simpa only [west, eW] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ .east
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) := hWNobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .south)))
          north := by
        symm
        simpa only [north, eN] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i, by omega⟩ ⟨j - 1, by omega⟩ .south
      _ = isingProj Complex.I north := by rw [hNS]
  · calc
      isingProj (-1) north = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .east)))
          north := by rw [hNE]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .east)) := by
        simpa only [north, eN] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i, by omega⟩ ⟨j - 1, by omega⟩ .east
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .north)) := hNEobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eE, .north)))
          east := by
        symm
        simpa only [east, eE] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i, by omega⟩ ⟨j, by omega⟩ .north
      _ = isingProj (-1) east := by rw [hEN]
  · calc
      isingProj (-Complex.I) east = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eE, .west)))
          east := by rw [hEW]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) := by
        simpa only [east, eE] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i, by omega⟩ ⟨j, by omega⟩ .west
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) := hESobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .north)))
          south := by
        symm
        simpa only [south, eS] using
          fkIsingSquareRadialPatchFullObservable_projection n m hn hm
            ⟨i - 1, by omega⟩ ⟨j, by omega⟩ .north
      _ = isingProj (-Complex.I) south := by rw [hSN]


theorem fkIsingSquareRadialPatchIncidence_top_eq_bottom
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m) :
    fkIsingSquareRadialPatchIncidence n m hn hm
        ⟨i, hi⟩ ⟨j, by omega⟩ (fkIsingSquareRadialPatchTopSide i j) =
      fkIsingSquareRadialPatchIncidence n m hn hm
        ⟨i, hi⟩ ⟨j + 1, hj⟩
        (fkIsingSquareRadialPatchBottomSide i (j + 1)) := by
  let a : Fin m := ⟨i, hi⟩
  let b : Fin m := ⟨j, by omega⟩
  let c : Fin m := ⟨j + 1, hj⟩
  let d : FKIsingSquareInteriorRadialDart n :=
    ⟨(fkIsingSquareRadialPatchEdge n m hm a b,
        fkIsingSquareRadialPatchTopSide i j),
      (fkIsingSquareRadialPatchCell n m hm a b).2 _⟩
  let e : FKIsingSquareInteriorRadialDart n :=
    ⟨(fkIsingSquareRadialPatchEdge n m hm a c,
        fkIsingSquareRadialPatchBottomSide i (j + 1)),
      (fkIsingSquareRadialPatchCell n m hm a c).2 _⟩
  change Quot.mk _ d = Quot.mk _ e
  apply Quot.sound
  have hstep : fkIsingSquareInteriorRadialBondPerm n hn d = e := by
    apply Subtype.ext
    change fkIsingSquareWiredBondMate n hn d.1 = e.1
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d.1 d.2]
    exact fkIsingSquareRadialPatch_bondMate_top n m hn hm i j hi hj
  have hcycle :=
    (Equiv.Perm.SameCycle.rfl :
      (fkIsingSquareInteriorRadialBondPerm n hn).SameCycle d d).apply_right
  simpa only [hstep] using hcycle

end
end StatMech.Universality
