/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc93extra.Part2
import Def.StatisticalMechanics.Code.Walls.rc94extra.Part2
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem rc94_A3_not_upper : ¬ rc80_IsUpper rc94_A3 := by
  intro h
  have hmem : (![false, false, false] : ConfigSpace (Fin 3)) ∈ rc94_A3 := by decide
  have := h _ hmem 1
  revert this
  decide


theorem rc94_A3_not_lower : ¬ rc80_IsLower rc94_A3 := by
  intro h
  have hmem : (![false, true, true] : ConfigSpace (Fin 3)) ∈ rc94_A3 := by decide
  have := h _ hmem 1
  revert this
  decide


theorem rc94_B3_not_upper : ¬ rc80_IsUpper rc94_B3 := by
  intro h
  have hmem : (![false, false, true] : ConfigSpace (Fin 3)) ∈ rc94_B3 := by decide
  have := h _ hmem 1
  revert this
  decide


theorem rc94_B3_not_lower : ¬ rc80_IsLower rc94_B3 := by
  intro h
  have hmem : (![true, false, false] : ConfigSpace (Fin 3)) ∈ rc94_B3 := by decide
  have := h _ hmem 0
  revert this
  decide


theorem rc94_A3_card : rc94_A3.card = 3 := by decide


theorem rc94_B3_card : rc94_B3.card = 5 := by decide


theorem rc94_A3_B3_inter_nonempty : (rc94_A3 ∩ rc94_B3).Nonempty := by decide


theorem rc94_A3_B3_interCoverA : rc94_InterCoverA rc94_A3 rc94_B3 := by
  unfold rc94_InterCoverA
  decide


theorem rc94_A3_B3_not_rc93 : ¬ rc93_InterCover rc94_A3 rc94_B3 := by
  intro h
  have hmem : (![true, false, false] : ConfigSpace (Fin 3)) ∈ rc94_A3 ∩ rc94_B3 := by decide
  have := h _ hmem
  revert this
  decide


theorem rc94_A3_B3_inter_not_subset_reflInterG :
    ¬ (rc94_A3 ∩ rc94_B3 ⊆ rc80_reflInterG rc94_A3 rc94_B3) := by decide


theorem rc94_A3_B3_not_reflCover : ¬ rc90_ReflCover rc94_A3 rc94_B3 := by
  intro h
  have hmem : (![true, false, false] : ConfigSpace (Fin 3)) ∈ rc94_A3 := by decide
  have := h _ hmem
  revert this
  decide


theorem rc94_A3_B3_disjOcc_nonempty : (rc80_disjOccG rc94_A3 rc94_B3).Nonempty := by decide


theorem rc94_nonmono_witness_fin3 :
    (rc80_disjOccG rc94_A3 rc94_B3).card ≤ (rc80_reflInterG rc94_A3 rc94_B3).card :=
  rc94_wall_interCoverA rc94_A3 rc94_B3 rc94_A3_B3_interCoverA


open Classical in


theorem rc94_status :
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        (rc80_reflInterG A B).card = (rc80_reflInterG B A).card) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc94_InterCoverA A B → A ∩ B ⊆ rc80_reflInterG B A) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc94_InterCoverA A B →
        (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc90_ComplClosed A → rc94_InterCoverA A B) ∧
    
    
    (¬ rc80_IsUpper rc94_A3 ∧ ¬ rc80_IsLower rc94_A3 ∧
        ¬ rc80_IsUpper rc94_B3 ∧ ¬ rc80_IsLower rc94_B3 ∧
        rc94_A3.card = 3 ∧ rc94_B3.card = 5 ∧
        (rc94_A3 ∩ rc94_B3).Nonempty ∧ rc94_InterCoverA rc94_A3 rc94_B3 ∧
        ¬ rc93_InterCover rc94_A3 rc94_B3 ∧
        ¬ (rc94_A3 ∩ rc94_B3 ⊆ rc80_reflInterG rc94_A3 rc94_B3) ∧
        ¬ rc90_ReflCover rc94_A3 rc94_B3 ∧
        (rc80_disjOccG rc94_A3 rc94_B3).Nonempty ∧
        (rc80_disjOccG rc94_A3 rc94_B3).card ≤ (rc80_reflInterG rc94_A3 rc94_B3).card) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun A B => rc94_reflInterG_card_symm A B,
   fun A B h => rc94_inter_subset_reflInterG_symm A B h,
   fun A B h => rc94_wall_interCoverA A B h,
   fun A B h => rc94_interCoverA_of_complClosed A B h,
   ⟨rc94_A3_not_upper, rc94_A3_not_lower, rc94_B3_not_upper, rc94_B3_not_lower,
    rc94_A3_card, rc94_B3_card, rc94_A3_B3_inter_nonempty, rc94_A3_B3_interCoverA,
    rc94_A3_B3_not_rc93, rc94_A3_B3_inter_not_subset_reflInterG,
    rc94_A3_B3_not_reflCover, rc94_A3_B3_disjOcc_nonempty, rc94_nonmono_witness_fin3⟩,
   rc82_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
