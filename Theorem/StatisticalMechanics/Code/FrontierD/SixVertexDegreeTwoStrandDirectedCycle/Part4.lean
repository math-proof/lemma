/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandDirectedCycle.Part4


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoStrandCyclePerm_isCycle
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed).IsCycle :=
  Equiv.Perm.isCycle_cycleOf _
    (sixVertexOrientedDegreeTwoStrandSuccessor_ne
      homega heta hdegree seed)

theorem sixVertexDegreeTwoStrandCyclePerm_seed_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    seed ∈ (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed).support := by
  rw [Equiv.Perm.mem_support]
  change (sixVertexOrientedDegreeTwoStrandSuccessor
    homega heta hdegree).cycleOf seed seed ≠ seed
  rw [Equiv.Perm.cycleOf_apply_self]
  exact sixVertexOrientedDegreeTwoStrandSuccessor_ne
    homega heta hdegree seed


end
end StatMech.FrontierD
