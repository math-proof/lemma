/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandDirectedCycle.Part5


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoStrandCycleEnumeration_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    Function.Injective (sixVertexDegreeTwoStrandCycleEnumeration
      homega heta hdegree seed) := by
  intro first second heq
  apply (sixVertexDegreeTwoStrandCycleEnumerationEquiv
    homega heta hdegree seed).injective
  exact Subtype.ext heq


theorem sixVertexDegreeTwoStrandCycleEnumeration_sameCycle
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (i : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed))) :
    (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed
        (sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree seed i) := by
  let cycle := sixVertexDegreeTwoStrandCyclePerm homega heta hdegree seed
  let enumerate := sixVertexDegreeTwoStrandCycleEnumerationEquiv
    homega heta hdegree seed
  have hmem : (enumerate i).1 ∈ cycle.support := (enumerate i).2
  by_contra hnot
  apply (Equiv.Perm.mem_support.mp hmem)
  exact Equiv.Perm.cycleOf_apply_of_not_sameCycle hnot

set_option maxHeartbeats 1000000 in

theorem sixVertexDegreeTwoStrandCycleEnumeration_next
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (i : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed))) :
    sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed
        (finitePeriodicSucc
          (orderOf_pos (sixVertexDegreeTwoStrandCyclePerm
            homega heta hdegree seed)) i) =
      sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree
        (sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree seed i) := by
  let cycle := sixVertexDegreeTwoStrandCyclePerm homega heta hdegree seed
  let enumerate := sixVertexDegreeTwoStrandCycleEnumerationEquiv
    homega heta hdegree seed
  have hcycle := sixVertexDegreeTwoStrandCyclePerm_isCycle
    homega heta hdegree seed
  have hnext := congrArg Subtype.val
    (permCycleFinEquivSupport_succ cycle hcycle
      ⟨seed, sixVertexDegreeTwoStrandCyclePerm_seed_mem
        homega heta hdegree seed⟩ i)
  have hsame :
      (sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree).SameCycle seed (enumerate i).1 := by
    exact sixVertexDegreeTwoStrandCycleEnumeration_sameCycle
      homega heta hdegree seed i
  have hsame' :
      (sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree).SameCycle seed
        (sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree seed i) := hsame
  calc
    sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed
        (finitePeriodicSucc
          (orderOf_pos (sixVertexDegreeTwoStrandCyclePerm
            homega heta hdegree seed)) i) = cycle (enumerate i).1 := by
      simpa only [cycle, enumerate,
        sixVertexDegreeTwoStrandCycleEnumeration,
        sixVertexDegreeTwoStrandCycleEnumerationEquiv] using hnext
    _ = sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree
        (sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree seed i) := by
      change (sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree).cycleOf seed
          (sixVertexDegreeTwoStrandCycleEnumeration
            homega heta hdegree seed i) = _
      rw [Equiv.Perm.cycleOf_apply, if_pos hsame']


end
end StatMech.FrontierD
