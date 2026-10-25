/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part7


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

def fkIsingSquareRadialPatchHorizontalSignedIncrement
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m) :
    Nat → Nat → Real :=
  fun i j ↦
    let x := fkIsingSquareInteriorRadialIncrement n hn
      (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j)
    if Even (i + j) then x else -x


def fkIsingSquareRadialPatchVerticalSignedIncrement
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m) :
    Nat → Nat → Real :=
  fun i j ↦
    let x := fkIsingSquareInteriorRadialIncrement n hn
      (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j)
    if Even (i + j) then x else -x


end
end StatMech.Universality
