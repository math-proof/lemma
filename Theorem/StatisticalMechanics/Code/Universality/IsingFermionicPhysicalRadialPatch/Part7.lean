/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part7


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

theorem fkIsingSquareRadialPatchHorizontalIncidence_bottom
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j < m) :
    fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j =
      fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
        (fkIsingSquareRadialPatchBottomSide i j) := by
  simp [fkIsingSquareRadialPatchHorizontalIncidence, hi, hj]

theorem fkIsingSquareRadialPatchHorizontalIncidence_top
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i : Nat) (hi : i < m) :
    fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i m =
      fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩
        (fkIsingSquareRadialPatchLast m hmpos)
        (fkIsingSquareRadialPatchTopSide i (m - 1)) := by
  simp [fkIsingSquareRadialPatchHorizontalIncidence, hi]

theorem fkIsingSquareRadialPatchVerticalIncidence_left
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j < m) :
    fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j =
      fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
        (fkIsingSquareRadialPatchLeftSide i j) := by
  simp [fkIsingSquareRadialPatchVerticalIncidence, hi, hj]

theorem fkIsingSquareRadialPatchVerticalIncidence_right
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (j : Nat) (hj : j < m) :
    fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos m j =
      fkIsingSquareRadialPatchIncidence n m hn hm
        (fkIsingSquareRadialPatchLast m hmpos) ⟨j, hj⟩
        (fkIsingSquareRadialPatchRightSide (m - 1) j) := by
  simp [fkIsingSquareRadialPatchVerticalIncidence, hj]

theorem fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j < m) :
    fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i (j + 1) =
      fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
        (fkIsingSquareRadialPatchTopSide i j) := by
  by_cases hnext : j + 1 < m
  · rw [fkIsingSquareRadialPatchHorizontalIncidence_bottom
      n m hn hm hmpos i (j + 1) hi hnext]
    exact (fkIsingSquareRadialPatchIncidence_top_eq_bottom
      n m hn hm i j hi hnext).symm
  · have heq : j + 1 = m := by omega
    subst m
    simpa [fkIsingSquareRadialPatchLast] using
      fkIsingSquareRadialPatchHorizontalIncidence_top
        n (j + 1) hn hm hmpos i hi

theorem fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j < m) :
    fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos (i + 1) j =
      fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
        (fkIsingSquareRadialPatchRightSide i j) := by
  by_cases hnext : i + 1 < m
  · rw [fkIsingSquareRadialPatchVerticalIncidence_left
      n m hn hm hmpos (i + 1) j hnext hj]
    exact (fkIsingSquareRadialPatchIncidence_right_eq_left
      n m hn hm i j hnext hj).symm
  · have heq : i + 1 = m := by omega
    subst m
    simpa [fkIsingSquareRadialPatchLast] using
      fkIsingSquareRadialPatchVerticalIncidence_right
        n (i + 1) hn hm hmpos j hj


end
end StatMech.Universality
