/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part8


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

theorem fkIsingSquareRadialPatchSignedIncrement_closed_on
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m) :
    IsingRectangleClosedOneFormOn
      (fkIsingSquareRadialPatchHorizontalSignedIncrement n m hn hm hmpos)
      (fkIsingSquareRadialPatchVerticalSignedIncrement n m hn hm hmpos)
      m m := by
  intro i hi j hj
  have hbottom := congrArg (fkIsingSquareInteriorRadialIncrement n hn)
    (fkIsingSquareRadialPatchHorizontalIncidence_bottom
      n m hn hm hmpos i j hi hj)
  have htop := congrArg (fkIsingSquareInteriorRadialIncrement n hn)
    (fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
      n m hn hm hmpos i j hi hj)
  have hleft := congrArg (fkIsingSquareInteriorRadialIncrement n hn)
    (fkIsingSquareRadialPatchVerticalIncidence_left
      n m hn hm hmpos i j hi hj)
  have hright := congrArg (fkIsingSquareInteriorRadialIncrement n hn)
    (fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
      n m hn hm hmpos i j hi hj)
  have hcell := fkIsingSquareInteriorRadialCell_increment_closed n hn
    (fkIsingSquareRadialPatchCell n m hm ⟨i, hi⟩ ⟨j, hj⟩)
  change fkIsingSquareInteriorRadialIncrement n hn
        (fkIsingSquareRadialPatchIncidence n m hn hm
          ⟨i, hi⟩ ⟨j, hj⟩ .west) +
      fkIsingSquareInteriorRadialIncrement n hn
        (fkIsingSquareRadialPatchIncidence n m hn hm
          ⟨i, hi⟩ ⟨j, hj⟩ .east) =
    fkIsingSquareInteriorRadialIncrement n hn
        (fkIsingSquareRadialPatchIncidence n m hn hm
          ⟨i, hi⟩ ⟨j, hj⟩ .south) +
      fkIsingSquareInteriorRadialIncrement n hn
        (fkIsingSquareRadialPatchIncidence n m hn hm
          ⟨i, hi⟩ ⟨j, hj⟩ .north) at hcell
  by_cases heven : Even (i + j)
  · have htopOdd : ¬ Even (i + (j + 1)) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    have hrightOdd : ¬ Even (i + 1 + j) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    simp only [fkIsingSquareRadialPatchHorizontalSignedIncrement,
      fkIsingSquareRadialPatchVerticalSignedIncrement, heven, htopOdd,
      hrightOdd, if_true, if_false]
    rw [hbottom, htop, hleft, hright]
    simp only [fkIsingSquareRadialPatchBottomSide,
      fkIsingSquareRadialPatchTopSide, fkIsingSquareRadialPatchLeftSide,
      fkIsingSquareRadialPatchRightSide, heven, if_true]
    linarith
  · have htopEven : Even (i + (j + 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    have hrightEven : Even (i + 1 + j) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    simp only [fkIsingSquareRadialPatchHorizontalSignedIncrement,
      fkIsingSquareRadialPatchVerticalSignedIncrement, heven, htopEven,
      hrightEven, if_true, if_false]
    rw [hbottom, htop, hleft, hright]
    simp only [fkIsingSquareRadialPatchBottomSide,
      fkIsingSquareRadialPatchTopSide, fkIsingSquareRadialPatchLeftSide,
      fkIsingSquareRadialPatchRightSide, heven, if_false]
    linarith


end
end StatMech.Universality
