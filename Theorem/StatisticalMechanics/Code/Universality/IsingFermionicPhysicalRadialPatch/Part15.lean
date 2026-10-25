/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part15


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

theorem fkIsingSquareRadialPatchPrimitive_laplacian_nonneg_of_even
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi0 : 0 < i) (hi1 : i + 1 ≤ m)
    (hj0 : 0 < j) (hj1 : j + 1 ≤ m)
    (heven : Even (i + j)) :
    0 ≤ fkIsingSquareRadialPatchLaplacian
      (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j := by
  have hi : i < m := by omega
  have hj : j < m := by omega
  have hleftOdd : ¬ Even (i - 1 + j) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hdownOdd : ¬ Even (i + (j - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hr := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos i j hi (by omega)
  have hl := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos (i - 1) j (by omega) (by omega)
  have hu := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i j
  have hd := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i (j - 1)
  simp only [fkIsingSquareRadialPatchHorizontalSignedIncrement,
    fkIsingSquareRadialPatchVerticalSignedIncrement, heven, hleftOdd,
    hdownOdd, if_true, if_false] at hr hl hu hd
  have hr0 := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j)
  have hl0 := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos (i - 1) j)
  have hu0 := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j)
  have hd0 := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i (j - 1))
  simp only [fkIsingSquareRadialPatchLaplacian]
  have hiSub : i - 1 + 1 = i := by omega
  have hjSub : j - 1 + 1 = j := by omega
  rw [hiSub] at hl
  rw [hjSub] at hd
  linarith


theorem fkIsingSquareRadialPatchPrimitive_laplacian_nonpos_of_odd
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi0 : 0 < i) (hi1 : i + 1 ≤ m)
    (hj0 : 0 < j) (hj1 : j + 1 ≤ m)
    (hodd : ¬ Even (i + j)) :
    fkIsingSquareRadialPatchLaplacian
      (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j ≤ 0 := by
  have hi : i < m := by omega
  have hj : j < m := by omega
  have hleftEven : Even (i - 1 + j) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hdownEven : Even (i + (j - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hr := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos i j hi (by omega)
  have hl := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos (i - 1) j (by omega) (by omega)
  have hu := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i j
  have hd := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i (j - 1)
  simp only [fkIsingSquareRadialPatchHorizontalSignedIncrement,
    fkIsingSquareRadialPatchVerticalSignedIncrement, hodd, hleftEven,
    hdownEven, if_true, if_false] at hr hl hu hd
  have hr0 := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j)
  have hl0 := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos (i - 1) j)
  have hu0 := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j)
  have hd0 := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i (j - 1))
  simp only [fkIsingSquareRadialPatchLaplacian]
  have hiSub : i - 1 + 1 = i := by omega
  have hjSub : j - 1 + 1 = j := by omega
  rw [hiSub] at hl
  rw [hjSub] at hd
  linarith

end
end StatMech.Universality
