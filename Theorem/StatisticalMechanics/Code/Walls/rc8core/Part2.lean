/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc8core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc7core.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Def.StatisticalMechanics.Code.Walls.rc8core.Part2
open Finset MeasureTheory
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc8_deficitBridge_iff_nonOpp :
    rc7_DeficitBridge ↔ rc8_DeficitBridgeNonOpp := by
  constructor
  · intro h n A B _; exact h n A B
  · intro h n A B
    by_cases hopp : (IsIncreasing A ∧ IsDecreasing B) ∨ (IsDecreasing A ∧ IsIncreasing B)
    · rcases hopp with ⟨hA, hB⟩ | ⟨hA, hB⟩
      · exact rc8_deficit_le_zero_inc_dec hA hB
      · exact rc8_deficit_le_zero_dec_inc hA hB
    · exact h n A B hopp


theorem rc8_reimerCardFormAll_of_nonOpp (h : rc8_DeficitBridgeNonOpp) : ReimerCardFormAll :=
  rc7_reimerCardFormAll_of_deficitBridge (rc8_deficitBridge_iff_nonOpp.mpr h)


open Classical in


theorem rc8_deficit_univ_univ :
    rc5_deficit (Set.univ : Set (ConfigSpace α)) Set.univ ≤ 0 :=
  rc8_deficit_le_zero_inc_dec (by simpa using isUpperSet_univ) (by simpa using isLowerSet_univ)


theorem rc8_cardform_oppositeMonotone :
    (∀ {A B : Set (ConfigSpace α)}, IsIncreasing A → IsDecreasing B → rc5_deficit A B ≤ 0)
      ∧ (∀ {A B : Set (ConfigSpace α)}, IsDecreasing A → IsIncreasing B → rc5_deficit A B ≤ 0)
      ∧ (rc7_DeficitBridge ↔ rc8_DeficitBridgeNonOpp)
      ∧ (rc8_DeficitBridgeNonOpp → ReimerCardFormAll) :=
  ⟨fun hA hB => rc8_deficit_le_zero_inc_dec hA hB,
    fun hA hB => rc8_deficit_le_zero_dec_inc hA hB,
    rc8_deficitBridge_iff_nonOpp,
    rc8_reimerCardFormAll_of_nonOpp⟩

end StatMech.Walls
