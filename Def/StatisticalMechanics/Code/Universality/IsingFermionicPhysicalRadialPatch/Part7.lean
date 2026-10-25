/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part6


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

def fkIsingSquareRadialPatchZero (m : Nat) (hm : 0 < m) : Fin m :=
  ⟨0, hm⟩

def fkIsingSquareRadialPatchLast (m : Nat) (hm : 0 < m) : Fin m :=
  ⟨m - 1, by omega⟩


def fkIsingSquareRadialPatchHorizontalIncidence
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m) :
    Nat → Nat → FKIsingSquareInteriorRadialIncidence n hn :=
  fun i j ↦
    if hi : i < m then
      if hj : j < m then
        fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
          (fkIsingSquareRadialPatchBottomSide i j)
      else
        fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩
          (fkIsingSquareRadialPatchLast m hmpos)
          (fkIsingSquareRadialPatchTopSide i (m - 1))
    else
      fkIsingSquareRadialPatchIncidence n m hn hm
        (fkIsingSquareRadialPatchZero m hmpos)
        (fkIsingSquareRadialPatchZero m hmpos) .west


def fkIsingSquareRadialPatchVerticalIncidence
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m) :
    Nat → Nat → FKIsingSquareInteriorRadialIncidence n hn :=
  fun i j ↦
    if hj : j < m then
      if hi : i < m then
        fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
          (fkIsingSquareRadialPatchLeftSide i j)
      else
        fkIsingSquareRadialPatchIncidence n m hn hm
          (fkIsingSquareRadialPatchLast m hmpos) ⟨j, hj⟩
          (fkIsingSquareRadialPatchRightSide (m - 1) j)
    else
      fkIsingSquareRadialPatchIncidence n m hn hm
        (fkIsingSquareRadialPatchZero m hmpos)
        (fkIsingSquareRadialPatchZero m hmpos) .west

end
end StatMech.Universality
