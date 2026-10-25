/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandDirectedCycle


namespace StatMech.FrontierD

noncomputable section

theorem permCycleFinEquivSupport_succ
    {D : Type*} [Fintype D] [DecidableEq D]
    (cycle : Equiv.Perm D) (hcycle : cycle.IsCycle)
    (seed : cycle.support) (i : Fin (orderOf cycle)) :
    permCycleFinEquivSupport cycle hcycle seed
        (finitePeriodicSucc (orderOf_pos cycle) i) =
      ⟨cycle (permCycleFinEquivSupport cycle hcycle seed i).1,
        Equiv.Perm.apply_mem_support.mpr
          (permCycleFinEquivSupport cycle hcycle seed i).2⟩ := by
  apply Subtype.ext
  change (cycle ^ ((i.val + 1) % orderOf cycle)) seed.1 =
    cycle ((cycle ^ i.val) seed.1)
  rw [pow_mod_orderOf]
  simp only [pow_succ', Equiv.Perm.mul_apply]


end
end StatMech.FrontierD
