/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part10


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

def fkIsingSquareRadialPatchDiagonalLaplacian
    (H : Nat → Nat → Real) (i j : Nat) : Real :=
  H (i + 1) (j + 1) + H (i + 1) (j - 1) +
    H (i - 1) (j - 1) + H (i - 1) (j + 1) - 4 * H i j


def fkIsingSquareRadialPatchPrimalIncrementDivergence
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) : Real :=
  let inc := fkIsingSquareInteriorRadialIncrement n hn
  inc (fkIsingSquareRadialPatchHorizontalIncidence
      n m hn hm hmpos i j) -
    inc (fkIsingSquareRadialPatchVerticalIncidence
      n m hn hm hmpos (i + 1) j) +
    inc (fkIsingSquareRadialPatchVerticalIncidence
      n m hn hm hmpos i (j - 1)) -
    inc (fkIsingSquareRadialPatchHorizontalIncidence
      n m hn hm hmpos i (j - 1)) +
    inc (fkIsingSquareRadialPatchHorizontalIncidence
      n m hn hm hmpos (i - 1) j) -
    inc (fkIsingSquareRadialPatchVerticalIncidence
      n m hn hm hmpos (i - 1) (j - 1)) +
    inc (fkIsingSquareRadialPatchVerticalIncidence
      n m hn hm hmpos i j) -
    inc (fkIsingSquareRadialPatchHorizontalIncidence
      n m hn hm hmpos (i - 1) (j + 1))


end
end StatMech.Universality
