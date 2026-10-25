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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part13
open Finset


namespace StatMech.FrontierD

noncomputable section

set_option maxHeartbeats 800000 in

theorem sum_map_permOrderedAllCycles
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (hsupport : sigma.support = Finset.univ)
    (f : D → Int) :
    ((permOrderedAllCycles sigma).map f).sum = ∑ d, f d := by
  classical
  unfold permOrderedAllCycles
  rw [sum_map_list_flatMap, sum_map_finset_toList]
  have hone : (∑ cycle ∈ sigma.cycleFactorsFinset,
      ((if hcycle : cycle ∈ sigma.cycleFactorsFinset then
          permOrderedCycleFactor sigma cycle hcycle else []).map f).sum) =
      ∑ cycle ∈ sigma.cycleFactorsFinset,
        ∑ d ∈ cycle.support, f d := by
    apply Finset.sum_congr rfl
    intro cycle hcycle
    rw [dif_pos hcycle, sum_map_permOrderedCycleFactor]
  rw [hone]
  have hdisjoint :
      (↑sigma.cycleFactorsFinset : Set (Equiv.Perm D)).PairwiseDisjoint
        (fun cycle => cycle.support) := by
    intro c hc d hd hcd
    exact (sigma.cycleFactorsFinset_pairwise_disjoint
      hc hd hcd).disjoint_support
  have hunion : sigma.cycleFactorsFinset.biUnion
      (fun cycle => cycle.support) = Finset.univ := by
    ext d
    rw [Finset.mem_biUnion]
    simp only [Finset.mem_univ, iff_true]
    rw [← Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset,
      hsupport]
    simp
  rw [← Finset.sum_biUnion hdisjoint, hunion]


end
end StatMech.FrontierD
