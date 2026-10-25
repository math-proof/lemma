/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc93extra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc90self.Part4
import Def.StatisticalMechanics.Code.Walls.rc93extra.Part2
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem rc93_A3_not_upper : ¬ rc80_IsUpper rc93_A3 := by
  intro h
  have hmem : (![false, false, false] : ConfigSpace (Fin 3)) ∈ rc93_A3 := by decide
  have := h _ hmem 0
  revert this
  decide


theorem rc93_A3_not_lower : ¬ rc80_IsLower rc93_A3 := by
  intro h
  have hmem : (![true, false, true] : ConfigSpace (Fin 3)) ∈ rc93_A3 := by decide
  have := h _ hmem 2
  revert this
  decide


theorem rc93_B3_not_upper : ¬ rc80_IsUpper rc93_B3 := by
  intro h
  have hmem : (![false, true, false] : ConfigSpace (Fin 3)) ∈ rc93_B3 := by decide
  have := h _ hmem 2
  revert this
  decide


theorem rc93_B3_not_lower : ¬ rc80_IsLower rc93_B3 := by
  intro h
  have hmem : (![true, false, true] : ConfigSpace (Fin 3)) ∈ rc93_B3 := by decide
  have := h _ hmem 0
  revert this
  decide


theorem rc93_A3_card : rc93_A3.card = 5 := by decide


theorem rc93_B3_card : rc93_B3.card = 3 := by decide


theorem rc93_A3_B3_inter_nonempty : (rc93_A3 ∩ rc93_B3).Nonempty := by decide


theorem rc93_A3_B3_interCover : rc93_InterCover rc93_A3 rc93_B3 := by
  unfold rc93_InterCover
  decide


theorem rc93_A3_B3_not_reflCover : ¬ rc90_ReflCover rc93_A3 rc93_B3 := by
  intro h
  have hmem : (![false, false, false] : ConfigSpace (Fin 3)) ∈ rc93_A3 := by decide
  have := h _ hmem
  revert this
  decide


theorem rc93_A3_B3_reflInterG_ne_A : rc80_reflInterG rc93_A3 rc93_B3 ≠ rc93_A3 := by decide


theorem rc93_A3_B3_disjOcc_nonempty : (rc80_disjOccG rc93_A3 rc93_B3).Nonempty := by decide


theorem rc93_nonmono_witness_fin3 :
    (rc80_disjOccG rc93_A3 rc93_B3).card ≤ (rc80_reflInterG rc93_A3 rc93_B3).card :=
  rc93_wall_interCover rc93_A3 rc93_B3 rc93_A3_B3_interCover


open Classical in


theorem rc93_status :
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc93_InterCover A B → A ∩ B ⊆ rc80_reflInterG A B) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc93_InterCover A B →
        (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc90_ReflCover A B → rc93_InterCover A B) ∧
    
    
    (¬ rc80_IsUpper rc93_A3 ∧ ¬ rc80_IsLower rc93_A3 ∧
        ¬ rc80_IsUpper rc93_B3 ∧ ¬ rc80_IsLower rc93_B3 ∧
        rc93_A3.card = 5 ∧ rc93_B3.card = 3 ∧
        (rc93_A3 ∩ rc93_B3).Nonempty ∧ rc93_InterCover rc93_A3 rc93_B3 ∧
        ¬ rc90_ReflCover rc93_A3 rc93_B3 ∧ rc80_reflInterG rc93_A3 rc93_B3 ≠ rc93_A3 ∧
        (rc80_disjOccG rc93_A3 rc93_B3).Nonempty ∧
        (rc80_disjOccG rc93_A3 rc93_B3).card ≤ (rc80_reflInterG rc93_A3 rc93_B3).card) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun A B h => rc93_inter_subset_reflInterG A B h,
   fun A B h => rc93_wall_interCover A B h,
   fun A B h => rc93_interCover_of_reflCover A B h,
   ⟨rc93_A3_not_upper, rc93_A3_not_lower, rc93_B3_not_upper, rc93_B3_not_lower,
    rc93_A3_card, rc93_B3_card, rc93_A3_B3_inter_nonempty, rc93_A3_B3_interCover,
    rc93_A3_B3_not_reflCover, rc93_A3_B3_reflInterG_ne_A,
    rc93_A3_B3_disjOcc_nonempty, rc93_nonmono_witness_fin3⟩,
   rc82_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
