/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part8


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


namespace finiteCRSFCycleSupport

theorem next_toWitness {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    finiteCRSFWitnessNext S.toWitness = next := by
  funext v
  by_cases hv : v ∈ S.carrier
  · have hne := S.ambientPerm_ne_of_mem hv
    change (if h : S.ambientPerm v = v then next v
      else S.ambientPerm.symm v) = next v
    rw [dif_neg hne]
    exact S.ambientPerm_symm_apply_of_mem hv
  · have heq := S.ambientPerm_apply_of_not_mem hv
    change (if h : S.ambientPerm v = v then next v
      else S.ambientPerm.symm v) = next v
    rw [dif_pos heq]


end finiteCRSFCycleSupport
end StatMech.FrontierA
