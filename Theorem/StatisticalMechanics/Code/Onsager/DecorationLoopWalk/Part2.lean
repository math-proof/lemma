/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk.Part4
import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleWeight
import Def.StatisticalMechanics.Code.Onsager.DecorationLoopWalk


namespace StatMech.Onsager

open Finset SimpleGraph

theorem ons_finsetExponent_toFinset_eq_edgeCount
    {E : Type*} [DecidableEq E] (l : List E) (hl : l.Nodup) :
    ons_finsetExponent l.toFinset =
      Multiset.toFinsupp (l : Multiset E) := by
  ext edge
  rw [ons_finsetExponent_apply, Multiset.toFinsupp_apply,
    Multiset.coe_count]
  by_cases hedge : edge ∈ l
  · rw [if_pos (List.mem_toFinset.mpr hedge)]
    simpa using (Multiset.count_eq_one_of_mem
      (show (l : Multiset E).Nodup from hl) hedge).symm
  · rw [if_neg (mt List.mem_toFinset.mp hedge)]
    exact (List.count_eq_zero.mpr hedge).symm

theorem ons_decTransitionExponent_eq_edgeCount
    (L : ℕ) [Fact (2 < L)] (d₂ d₁ : ons_Dart L)
    (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
    ons_decTransitionExponent L d₂ d₁ =
      ons_decWalkEdgeCount
        (ons_decTransitionWalk L d₂ d₁ hstep) := by
  rw [ons_decTransitionExponent_eq_walkEdges]
  exact ons_finsetExponent_toFinset_eq_edgeCount _
    ((SimpleGraph.Walk.isTrail_def _).mp
      (ons_decTransitionWalk_isTrail L d₂ d₁ hstep))

end StatMech.Onsager
