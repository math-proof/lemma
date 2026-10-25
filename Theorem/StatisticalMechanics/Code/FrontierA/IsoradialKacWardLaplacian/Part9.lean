/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part10


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


namespace finiteCRSFCycleSupport

theorem mem_atomicCycles_isCycle {next : V -> V}
    (S : finiteCRSFCycleSupport next) {cycle : Equiv.Perm (↑S.carrier)}
    (hcycle : cycle ∈ S.atomicCycles) : cycle.IsCycle :=
  (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).1


theorem exists_mem_atomicCycle {next : V -> V}
    (S : finiteCRSFCycleSupport next) (v : ↑S.carrier) :
    ∃ cycle ∈ S.atomicCycles, v ∈ cycle.support := by
  change ∃ cycle ∈ S.restrictedPerm.cycleFactorsFinset,
    v ∈ cycle.support
  rw [← Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset,
    S.restrictedPerm_support]
  simp


theorem atomicCycle_apply {next : V -> V}
    (S : finiteCRSFCycleSupport next) {cycle : Equiv.Perm (↑S.carrier)}
    (hcycle : cycle ∈ S.atomicCycles) (v : ↑S.carrier)
    (hv : v ∈ cycle.support) : (cycle v : V) = next v := by
  have hrestrict := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).2 v hv
  exact congrArg Subtype.val hrestrict


end finiteCRSFCycleSupport
end StatMech.FrontierA
