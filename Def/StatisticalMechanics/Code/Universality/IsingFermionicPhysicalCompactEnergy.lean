/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part15


namespace StatMech.Universality

open Finset

noncomputable section

def fkIsingSquareRadialPatchPrimitiveCellTotalVariation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) : Real :=
  |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j -
      fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| +
    |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) (j + 1) -
      fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1)| +
    |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1) -
      fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| +
    |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) (j + 1) -
      fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j|


def fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) : Real :=
  |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) (j + 1) -
      fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| +
    |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j -
      fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1)|


end
end StatMech.Universality
