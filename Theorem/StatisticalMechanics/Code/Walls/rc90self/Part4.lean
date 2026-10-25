/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc89nested.Part3
import Def.StatisticalMechanics.Code.Walls.rc90self.Part4
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem rc90_A3_B3_reflCover : rc90_ReflCover rc90_A3 rc90_B3 := by
  intro a ha
  fin_cases ha <;> decide


theorem rc90_A3_not_upper : ¬ rc80_IsUpper rc90_A3 := by
  intro h
  have hmem : (![false, false, false] : ConfigSpace (Fin 3)) ∈ rc90_A3 := by decide
  have := h _ hmem 0
  revert this
  decide


theorem rc90_A3_not_lower : ¬ rc80_IsLower rc90_A3 := by
  intro h
  have hmem : (![false, true, true] : ConfigSpace (Fin 3)) ∈ rc90_A3 := by decide
  have := h _ hmem 2
  revert this
  decide


theorem rc90_B3_not_upper : ¬ rc80_IsUpper rc90_B3 := by
  intro h
  have hmem : (![false, true, false] : ConfigSpace (Fin 3)) ∈ rc90_B3 := by decide
  have := h _ hmem 2
  revert this
  decide


theorem rc90_B3_not_lower : ¬ rc80_IsLower rc90_B3 := by
  intro h
  have hmem : (![true, true, true] : ConfigSpace (Fin 3)) ∈ rc90_B3 := by decide
  have := h _ hmem 0
  revert this
  decide


theorem rc90_A3_card : rc90_A3.card = 3 := by decide


theorem rc90_B3_card : rc90_B3.card = 5 := by decide


theorem rc90_A3_B3_disjOcc_nonempty : (rc80_disjOccG rc90_A3 rc90_B3).Nonempty := by decide


theorem rc90_nonmono_witness_fin3 :
    (rc80_disjOccG rc90_A3 rc90_B3).card ≤ (rc80_reflInterG rc90_A3 rc90_B3).card :=
  rc90_wall_reflCover rc90_A3 rc90_B3 rc90_A3_B3_reflCover


open Classical in


theorem rc90_status :
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc90_ReflCover A B → rc80_reflInterG A B = A) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc90_ReflCover A B →
        (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)),
        rc90_ComplClosed A →
        (rc80_disjOccG A A).card ≤ (rc80_reflInterG A A).card) ∧
    
    (¬ (rc80_disjOccG rc90_Aself rc90_Aself ⊆ rc80_reflInterG rc90_Aself rc90_Aself)) ∧
    
    (¬ rc80_IsUpper rc90_A3 ∧ ¬ rc80_IsLower rc90_A3 ∧
        ¬ rc80_IsUpper rc90_B3 ∧ ¬ rc80_IsLower rc90_B3 ∧
        rc90_A3.card = 3 ∧ rc90_B3.card = 5 ∧ rc90_ReflCover rc90_A3 rc90_B3 ∧
        (rc80_disjOccG rc90_A3 rc90_B3).Nonempty ∧
        (rc80_disjOccG rc90_A3 rc90_B3).card ≤ (rc80_reflInterG rc90_A3 rc90_B3).card) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun A B h => rc90_reflInterG_eq_left_of_cover A B h,
   fun A B h => rc90_wall_reflCover A B h,
   fun A h => rc90_wall_self_complClosed A h,
   rc90_self_diagonal_true_but_needs_injection,
   ⟨rc90_A3_not_upper, rc90_A3_not_lower, rc90_B3_not_upper, rc90_B3_not_lower,
    rc90_A3_card, rc90_B3_card, rc90_A3_B3_reflCover, rc90_A3_B3_disjOcc_nonempty,
    rc90_nonmono_witness_fin3⟩,
   rc82_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
