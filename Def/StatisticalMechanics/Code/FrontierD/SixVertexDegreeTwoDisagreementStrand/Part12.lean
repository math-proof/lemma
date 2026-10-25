/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentCType.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part10
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def permCycleFinEquivSupport
    {D : Type*} [Fintype D] [DecidableEq D]
    (cycle : Equiv.Perm D) (hcycle : cycle.IsCycle)
    (seed : cycle.support) : Fin (orderOf cycle) ≃ cycle.support := by
  let forward : Fin (orderOf cycle) → cycle.support := fun k =>
    ⟨(cycle ^ k.val) seed.1,
      Equiv.Perm.pow_apply_mem_support.mpr seed.2⟩
  apply Equiv.ofBijective forward
  apply (Fintype.bijective_iff_surjective_and_card forward).mpr
  constructor
  · intro target
    have hsame := hcycle.sameCycle
      (Equiv.Perm.mem_support.mp seed.2)
      (Equiv.Perm.mem_support.mp target.2)
    obtain ⟨k, hk⟩ := hsame.exists_fin_pow_eq
    exact ⟨k, Subtype.ext hk⟩
  · simp only [Fintype.card_fin, Fintype.card_coe, hcycle.orderOf]


noncomputable def permOrderedCycleFactor
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma cycle : Equiv.Perm D)
    (hcycle : cycle ∈ sigma.cycleFactorsFinset) : List D :=
  let hc : cycle.IsCycle :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).1
  let hs : cycle.support.Nonempty := hc.nonempty_support
  let seed : cycle.support :=
    ⟨Classical.choose hs, Classical.choose_spec hs⟩
  List.ofFn fun k => (permCycleFinEquivSupport cycle hc seed k).1

end
end StatMech.FrontierD
