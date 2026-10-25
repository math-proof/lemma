/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc82fixedordercompress.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc81shifttomonotone.Part3
import Def.StatisticalMechanics.Code.Walls.rc82fixedordercompress.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem rc82_reflInter_orig_zero : (rc80_reflInterG rc82_wA rc82_wA).card = 0 := by decide


theorem rc82_downClosure_wA_univ :
    rc81_downClosure rc82_wA = (Finset.univ : Finset (ConfigSpace (Fin 2))) := by decide


theorem rc82_reflInter_shifted_one :
    (rc80_reflInterG (rc81_downClosure rc82_wA) rc82_wA).card = 1 := by decide


theorem rc82_downup_shift_refutes_wall_witness :
    (rc80_reflInterG rc82_wA rc82_wA).card
      < (rc80_reflInterG (rc81_downClosure rc82_wA) rc82_wA).card := by
  rw [rc82_reflInter_orig_zero, rc82_reflInter_shifted_one]; exact Nat.zero_lt_one


theorem rc82_lowerWitness : rc80_IsLower ({rc81_botF} : Finset (ConfigSpace (Fin 2))) :=
  rc80_monoWitness_lower

theorem rc82_upperWitness : rc80_IsUpper ({rc82_topF} : Finset (ConfigSpace (Fin 2))) :=
  rc80_monoWitness_upper


theorem rc82_dualWitness_reduces :
    rc80_disjOccG ({rc81_botF} : Finset (ConfigSpace (Fin 2))) {rc82_topF}
      = ({rc81_botF} : Finset (ConfigSpace (Fin 2))) ∩ {rc82_topF} :=
  rc82_disjOccG_eq_inter_of_lower_upper rc82_lowerWitness rc82_upperWitness

open Classical in


theorem rc82_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc81_reimerWprobCore_of_boxUnionBound h

open Classical in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in 


theorem rc82_status :
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (A : Finset (ConfigSpace ι)),
        (rc82_downCompressA i A).card = A.card) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (B : Finset (ConfigSpace ι)),
        (rc82_upCompressB i B).card = B.card) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc80_IsLower A → rc80_IsUpper B → rc80_disjOccG A B = A ∩ B) ∧
    
    (∀ A B : Finset (ConfigSpace (Fin 2)),
        (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card) ∧
    
    ((rc80_reflInterG rc82_wA rc82_wA).card
        < (rc80_reflInterG (rc81_downClosure rc82_wA) rc82_wA).card) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun i A => rc82_downCompressA_card i A,
   fun i B => rc82_upCompressB_card i B,
   fun _ _ hA hB => rc82_disjOccG_eq_inter_of_lower_upper hA hB,
   rc82_wall_holds_everywhere_fin2,
   rc82_downup_shift_refutes_wall_witness,
   rc82_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
