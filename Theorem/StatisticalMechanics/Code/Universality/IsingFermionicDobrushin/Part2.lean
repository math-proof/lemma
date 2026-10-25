/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingSHolo.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part3
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

variable (P : PlanarZ2Subgraph) (M : Type*) [Fintype M] [DecidableEq M]


namespace FKIsingDobrushinDomain

variable {P M} (D : FKIsingDobrushinDomain P M)


theorem criticalMass_nonneg (omega : ConfigSpace (Sym2 P.V)) :
    0 <= D.criticalMass omega := by
  exact bcProb_nonneg P.G D.wiring fkIsingCriticalParameter_mem_Ioo.1
    fkIsingCriticalParameter_mem_Ioo.2 (by norm_num) omega

theorem criticalMass_sum_eq_one :
    ∑ omega : ConfigSpace (Sym2 P.V), D.criticalMass omega = 1 := by
  exact bcProb_sum_eq_one P.G D.wiring fkIsingCriticalParameter_mem_Ioo.1
    fkIsingCriticalParameter_mem_Ioo.2 (by norm_num)


end FKIsingDobrushinDomain
end
end StatMech.Universality
