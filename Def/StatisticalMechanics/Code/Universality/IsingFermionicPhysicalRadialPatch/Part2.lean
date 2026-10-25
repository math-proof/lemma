/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

def fkIsingSquareRadialPatchVertex
    (n m : Nat) (hm : m ≤ n) (i j : Fin m) :
    (fkSquareBoxPlanar n).V := by
  let q := fkIsingSquareRadialPatchHalf i.1 j.1
  have hq : q < n := fkIsingSquareRadialPatchHalf_lt hm i j
  refine ⟨![(q : Int), (i.1 : Int) - (q : Int)], ?_⟩
  intro k
  fin_cases k
  · simpa using Nat.le_of_lt hq
  · exact Nat.le_trans
      (Int.natAbs_coe_sub_coe_lt_of_lt
        (lt_of_lt_of_le i.2 hm) hq).le
      (Nat.le_refl n)


def fkIsingSquareRadialPatchDirection (i j : Nat) :
    FKIsingSquareDirection :=
  if Even (i + j) then .east else .north

end
end StatMech.Universality
