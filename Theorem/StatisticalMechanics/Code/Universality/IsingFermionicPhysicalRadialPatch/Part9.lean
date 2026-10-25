/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part9


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

theorem fkIsingSquareRadialPatchPrimitive_horizontal_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j ≤ m) :
    fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j -
        fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j =
      fkIsingSquareRadialPatchHorizontalSignedIncrement
        n m hn hm hmpos i j := by
  exact isingRectanglePrimitive_horizontal_increment_on _ _ m m
    (fkIsingSquareRadialPatchSignedIncrement_closed_on n m hn hm hmpos)
    i j hi hj

theorem fkIsingSquareRadialPatchPrimitive_vertical_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) :
    fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1) -
        fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j =
      fkIsingSquareRadialPatchVerticalSignedIncrement
        n m hn hm hmpos i j := by
  exact isingRectanglePrimitive_vertical_increment _ _ i j


theorem fkIsingSquareRadialPatchPrimitive_abs_horizontal_sub_eq_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j ≤ m) :
    |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j -
        fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| =
      fkIsingSquareInteriorRadialIncrement n hn
        (fkIsingSquareRadialPatchHorizontalIncidence
          n m hn hm hmpos i j) := by
  rw [fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos i j hi hj]
  have hnonneg := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j)
  by_cases heven : Even (i + j)
  · simp [fkIsingSquareRadialPatchHorizontalSignedIncrement,
      heven, abs_of_nonneg hnonneg]
  · simp [fkIsingSquareRadialPatchHorizontalSignedIncrement,
      heven, abs_of_nonneg hnonneg]


theorem fkIsingSquareRadialPatchPrimitive_abs_vertical_sub_eq_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) :
    |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1) -
        fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| =
      fkIsingSquareInteriorRadialIncrement n hn
        (fkIsingSquareRadialPatchVerticalIncidence
          n m hn hm hmpos i j) := by
  rw [fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i j]
  have hnonneg := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j)
  by_cases heven : Even (i + j)
  · simp [fkIsingSquareRadialPatchVerticalSignedIncrement,
      heven, abs_of_nonneg hnonneg]
  · simp [fkIsingSquareRadialPatchVerticalSignedIncrement,
      heven, abs_of_nonneg hnonneg]


theorem fkIsingSquareRadialPatch_two_mul_normSq_full_eq_cell_totalVariation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j < m) :
    2 * Complex.normSq
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, hi⟩ ⟨j, hj⟩) =
      |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j -
          fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| +
        |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) (j + 1) -
          fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1)| +
        |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1) -
          fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| +
        |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) (j + 1) -
          fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j| := by
  have hbottom :=
    fkIsingSquareRadialPatchPrimitive_abs_horizontal_sub_eq_increment
      n m hn hm hmpos i j hi (by omega)
  have htop :=
    fkIsingSquareRadialPatchPrimitive_abs_horizontal_sub_eq_increment
      n m hn hm hmpos i (j + 1) hi (by omega)
  have hleft :=
    fkIsingSquareRadialPatchPrimitive_abs_vertical_sub_eq_increment
      n m hn hm hmpos i j
  have hright :=
    fkIsingSquareRadialPatchPrimitive_abs_vertical_sub_eq_increment
      n m hn hm hmpos (i + 1) j
  rw [fkIsingSquareRadialPatchHorizontalIncidence_bottom
      n m hn hm hmpos i j hi hj] at hbottom
  rw [fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
      n m hn hm hmpos i j hi hj] at htop
  rw [fkIsingSquareRadialPatchVerticalIncidence_left
      n m hn hm hmpos i j hi hj] at hleft
  rw [fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
      n m hn hm hmpos i j hi hj] at hright
  have hhorizontal :=
    fkIsingSquareRadialPatch_normSq_full_eq_bottom_add_top_increment
      n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
  have hvertical :=
    fkIsingSquareRadialPatch_normSq_full_eq_left_add_right_increment
      n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
  rw [← hbottom, ← htop] at hhorizontal
  rw [← hleft, ← hright] at hvertical
  calc
    2 * Complex.normSq
        (fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, hi⟩ ⟨j, hj⟩) =
        Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm
              ⟨i, hi⟩ ⟨j, hj⟩) +
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm
              ⟨i, hi⟩ ⟨j, hj⟩) := by ring
    _ = _ := by
      nth_rewrite 1 [hhorizontal]
      rw [hvertical]
      ring


end
end StatMech.Universality
