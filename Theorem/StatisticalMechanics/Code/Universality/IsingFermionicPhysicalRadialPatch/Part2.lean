/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

theorem fkIsingSquareRadialPatchDirection_available
    (n m : Nat) (hm : m ≤ n) (i j : Fin m) :
    fkIsingSquareDirectionAvailable n
      (fkIsingSquareRadialPatchVertex n m hm i j)
      (fkIsingSquareRadialPatchDirection i.1 j.1) := by
  have hi : i.1 < n := lt_of_lt_of_le i.2 hm
  have hq := fkIsingSquareRadialPatchHalf_lt hm i j
  by_cases heven : Even (i.1 + j.1)
  · simp [fkIsingSquareRadialPatchDirection, heven,
      fkIsingSquareDirectionAvailable, fkIsingSquareRadialPatchVertex]
    exact_mod_cast hq
  · simp [fkIsingSquareRadialPatchDirection, heven,
      fkIsingSquareDirectionAvailable, fkIsingSquareRadialPatchVertex]
    omega


end
end StatMech.Universality
