/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part8
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.Part6


namespace StatMech.Ising.LPRankFiveDegreeTwoCycleOverlapObstruction

theorem flip_ne (y : Target) : flip y ≠ y := by
  fin_cases y <;> decide

theorem flip_involutive (y : Target) : flip (flip y) = y := by
  fin_cases y <;> decide


theorem every_source_degree_two (z : StrictSource) :
    (candidates z).card = 2 := by
  fin_cases z <;> decide


theorem both_mates_have_no_degree_one_incoming (y : Target) :
    (incomingDegree 1 y).card = 0 ∧
      (incomingDegree 1 (flip y)).card = 0 := by
  fin_cases y <;> decide


theorem incoming_classification (y : Target) :
    (incomingDegree 1 y).card = 0 ∧
      (incomingDegree 2 y).card ≤ 2 := by
  fin_cases y <;> decide


theorem strict_component_saturated (y : Target) :
    Fintype.card StrictSource = (component y).card := by
  fin_cases y <;> decide


theorem no_component_slack_for_handled (y : Target) :
    ¬ 1 + Fintype.card StrictSource ≤ (component y).card := by
  fin_cases y <;> decide

theorem not_combined_card_le_target :
    ¬ Fintype.card (HandledSource ⊕ StrictSource) ≤
      Fintype.card Target := by
  decide

end StatMech.Ising.LPRankFiveDegreeTwoCycleOverlapObstruction
