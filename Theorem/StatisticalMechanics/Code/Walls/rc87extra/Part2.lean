/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc87extra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc85smallfamily
import Def.StatisticalMechanics.Code.Walls.rc87extra
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem rc87_B3_not_upper : ¬ rc80_IsUpper rc87_B3 := by
  intro h
  have hmem : (fun _ => false : ConfigSpace (Fin 3)) ∈ rc87_B3 := by
    simp [rc87_B3]
  have := h _ hmem 0
  
  revert this
  decide


theorem rc87_B3_not_lower : ¬ rc80_IsLower rc87_B3 := by
  intro h
  have hmem : (fun _ => true : ConfigSpace (Fin 3)) ∈ rc87_B3 := by
    simp [rc87_B3]
  have := h _ hmem 0
  revert this
  decide


theorem rc87_nonmono_witness_fin3 :
    (rc80_disjOccG (Finset.univ : Finset (ConfigSpace (Fin 3))) rc87_B3).card
      = (rc80_reflInterG (Finset.univ : Finset (ConfigSpace (Fin 3))) rc87_B3).card :=
  rc87_wall_univ_left_eq rc87_B3


open Classical in


theorem rc87_status :
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)),
        rc80_disjOccG (Finset.univ : Finset (ConfigSpace ι)) B = B) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)),
        rc80_disjOccG A (Finset.univ : Finset (ConfigSpace ι)) = A) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)),
        (rc80_reflInterG (Finset.univ : Finset (ConfigSpace ι)) B).card = B.card) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)),
        rc80_reflInterG A (Finset.univ : Finset (ConfigSpace ι)) = A) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)),
        (rc80_disjOccG (Finset.univ : Finset (ConfigSpace ι)) B).card
          ≤ (rc80_reflInterG (Finset.univ : Finset (ConfigSpace ι)) B).card) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)),
        (rc80_disjOccG A (Finset.univ : Finset (ConfigSpace ι))).card
          ≤ (rc80_reflInterG A (Finset.univ : Finset (ConfigSpace ι))).card) ∧
    
    (¬ rc80_IsUpper rc87_B3 ∧ ¬ rc80_IsLower rc87_B3 ∧
        (rc80_disjOccG (Finset.univ : Finset (ConfigSpace (Fin 3))) rc87_B3).card
          = (rc80_reflInterG (Finset.univ : Finset (ConfigSpace (Fin 3))) rc87_B3).card) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun B => rc87_disjOccG_univ_left B,
   fun A => rc87_disjOccG_univ_right A,
   fun B => rc87_reflInterG_univ_left_card B,
   fun A => rc87_reflInterG_univ_right_eq A,
   fun B => rc87_wall_univ_left B,
   fun A => rc87_wall_univ_right A,
   ⟨rc87_B3_not_upper, rc87_B3_not_lower, rc87_nonmono_witness_fin3⟩,
   rc82_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
