/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc87extra.Part2
import Def.StatisticalMechanics.Code.Walls.rc88twogen
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 800000

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem rc88_a3_ne_b3 : rc88_a3 ≠ rc88_b3 := by decide


theorem rc88_A3_not_upper : ¬ rc80_IsUpper rc88_A3 := by
  intro h
  have hmem : rc88_a3 ∈ rc88_A3 := by decide
  have := h _ hmem 2
  revert this
  decide


theorem rc88_A3_not_lower : ¬ rc80_IsLower rc88_A3 := by
  intro h
  have hmem : rc88_a3 ∈ rc88_A3 := by decide
  have := h _ hmem 1
  revert this
  decide


theorem rc88_nonmono_witness_fin3 (B : Finset (ConfigSpace (Fin 3))) :
    (rc80_disjOccG rc88_A3 B).card ≤ (rc80_reflInterG rc88_A3 B).card :=
  rc88_wall_twogen_left rc88_a3 rc88_b3 B


theorem rc88_A3_card : rc88_A3.card = 2 := by decide


open Classical in


theorem rc88_status :
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι)),
        rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B ⊆ ({a, b} : Finset (ConfigSpace ι))) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι)),
        a ∈ rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B → rc80_compl b ∈ B) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι)),
        (rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B).card
          ≤ (rc80_reflInterG ({a, b} : Finset (ConfigSpace ι)) B).card) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)) (a b : ConfigSpace ι),
        (rc80_disjOccG A ({a, b} : Finset (ConfigSpace ι))).card
          ≤ (rc80_reflInterG A ({a, b} : Finset (ConfigSpace ι))).card) ∧
    
    (¬ rc80_IsUpper rc88_A3 ∧ ¬ rc80_IsLower rc88_A3 ∧ rc88_A3.card = 2 ∧
        (rc80_disjOccG rc88_A3 Finset.univ).card
          ≤ (rc80_reflInterG rc88_A3 Finset.univ).card) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun a b B => rc88_disjOccG_pair_subset a b B,
   fun a b B ha => rc88_core_other a b B ha,
   fun a b B => rc88_wall_twogen_left a b B,
   fun A a b => rc88_wall_twogen_right A a b,
   ⟨rc88_A3_not_upper, rc88_A3_not_lower, rc88_A3_card, rc88_nonmono_witness_fin3 Finset.univ⟩,
   rc82_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
