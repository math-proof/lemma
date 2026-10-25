/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part8
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.Part2


namespace StatMech.Ising.LPRankFiveHandledStrictOverlapObstruction

theorem flip_ne (y : Target) : flip y ≠ y := by
  fin_cases y <;> decide

theorem flip_involutive (y : Target) : flip (flip y) = y := by
  fin_cases y <;> decide

theorem center_injective : Function.Injective center := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide


theorem center_ne_flip_center (a b : HandledSource) :
    center a ≠ flip (center b) := by
  fin_cases a <;> fin_cases b <;> decide


theorem candidates_card_eq_one_or_two (z : StrictSource) :
    (candidates z).card = 1 ∨ (candidates z).card = 2 := by
  fin_cases z <;> decide


theorem incoming_classification (y : Target) :
    ((incomingDegree 1 y).card = 0 ∧
        (incomingDegree 2 y).card ≤ 2) ∨
      ((incomingDegree 1 y).card = 1 ∧
        (incomingDegree 2 y).card = 0) := by
  fin_cases y <;> decide


theorem one_add_incoming_card_le_rerouteNeighborhood (y : Target) :
    1 + (incoming y).card ≤ (rerouteNeighborhood y).card := by
  fin_cases y <;> decide


theorem chosen_rerouteNeighborhoods_not_disjoint :
    ¬ Disjoint (rerouteNeighborhood (center 0))
      (rerouteNeighborhood (center 1)) := by
  decide


theorem not_combined_card_le_target :
    ¬ Fintype.card (HandledSource ⊕ StrictSource) ≤
      Fintype.card Target := by
  decide

end StatMech.Ising.LPRankFiveHandledStrictOverlapObstruction
