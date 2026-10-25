/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part9


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


namespace finiteCRSFCycleSupport

noncomputable def toAtomicCycle {next : V -> V}
    (S : finiteCRSFCycleSupport next)
    (cycle : {cycle // cycle ∈ S.atomicCycles}) :
    finiteCRSFAtomicCycle next := by
  refine ⟨Equiv.Perm.ofSubtype cycle.1, ?_, ?_⟩
  · change (cycle.1.extendDomain (Equiv.refl (↑S.carrier))).IsCycle
    exact (S.mem_atomicCycles_isCycle cycle.2).extendDomain _
  · intro v hv
    have hvcarrier : v ∈ S.carrier := by
      by_contra hcarrier
      exact (Equiv.Perm.mem_support.mp hv)
        (Equiv.Perm.ofSubtype_apply_of_not_mem _ hcarrier)
    let w : ↑S.carrier := ⟨v, hvcarrier⟩
    have hw : w ∈ cycle.1.support := by
      rw [Equiv.Perm.mem_support]
      intro hfixed
      apply Equiv.Perm.mem_support.mp hv
      rw [Equiv.Perm.ofSubtype_apply_of_mem _ hvcarrier]
      exact congrArg Subtype.val hfixed
    rw [Equiv.Perm.ofSubtype_apply_of_mem _ hvcarrier]
    exact S.atomicCycle_apply cycle.2 w hw

noncomputable def atomicCycleEmbedding {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    {cycle // cycle ∈ S.atomicCycles} ↪ finiteCRSFAtomicCycle next where
  toFun := S.toAtomicCycle
  inj' := by
    intro cycle cycle' h
    apply Subtype.ext
    exact Equiv.Perm.ofSubtype_injective (congrArg Subtype.val h)


noncomputable def toAtomicCycles {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    Finset (finiteCRSFAtomicCycle next) :=
  Finset.univ.map S.atomicCycleEmbedding

end finiteCRSFCycleSupport
end StatMech.FrontierA
