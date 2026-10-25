/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

theorem fkIsingSquareRadialPatchHalf_eq (i j : Nat) :
    fkIsingSquareRadialPatchHalf i j = (i + j + 1) / 2 := rfl

theorem fkIsingSquareRadialPatchHalf_lt
    {n m : Nat} (hm : m ≤ n) (i j : Fin m) :
    fkIsingSquareRadialPatchHalf i.1 j.1 < n := by
  unfold fkIsingSquareRadialPatchHalf
  rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
  have hi := i.2
  have hj := j.2
  omega


end
end StatMech.Universality
