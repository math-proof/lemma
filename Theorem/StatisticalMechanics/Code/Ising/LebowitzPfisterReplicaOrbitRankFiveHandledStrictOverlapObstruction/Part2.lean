/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part8
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.Part4


namespace StatMech.Ising.LPRankFiveMultiplicityMateOverlapObstruction

theorem flip_ne (y : Target) : flip y ≠ y := by
  fin_cases y <;> decide

theorem flip_involutive (y : Target) : flip (flip y) = y := by
  fin_cases y <;> decide

theorem every_source_degree_one (z : StrictSource) :
    (candidates z).card = 1 := by
  fin_cases z <;> decide

theorem every_target_has_one_degree_one_incoming (y : Target) :
    (incoming y).card = 1 := by
  fin_cases y <;> decide

theorem local_center_capacity :
    1 + (incoming (center ())).card ≤ (component (center ())).card := by
  decide


theorem mate_closed_component_has_no_extra_capacity :
    (pairIncoming (center ())).card = (component (center ())).card ∧
      ¬ 1 + (pairIncoming (center ())).card ≤
        (component (center ())).card := by
  decide

theorem not_combined_card_le_target :
    ¬ Fintype.card (HandledSource ⊕ StrictSource) ≤
      Fintype.card Target := by
  decide

end StatMech.Ising.LPRankFiveMultiplicityMateOverlapObstruction
