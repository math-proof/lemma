/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc77configmeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part7
import Def.StatisticalMechanics.Code.Walls.rc77configmeasure.Part4
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in


theorem rc77_fixpoint_wall_fin2 :
    ∀ A B : Finset (ConfigSpace (Fin 2)),
      rc77_isDownEvt A = true → rc77_isUpEvt B = true →
      2 ^ 2 * (rc75_disjOccF A B).card ≤ A.card * B.card := by
  decide


set_option maxRecDepth 8000 in


theorem rc77_witness_nonvacuous :
    (rc75_disjOccF (rc77_downEvt 1 rc77_wA) (rc77_upEvt 1 rc77_wB)).Nonempty := by
  decide


open Classical in


theorem rc77_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc75_reimerWprobCore_of_boxUnionBound h

open Classical in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in


theorem rc77_status :
    
    ((rc75_disjOccF rc77_wA rc77_wB).card = 0
      ∧ (rc75_disjOccF (rc77_downEvt 1 rc77_wA) (rc77_upEvt 1 rc77_wB)).card = 1) ∧
    
    (rc77_downUpIncreases = 56 ∧ rc77_downUpDecreases = 0) ∧
    
    (rc77_incCount rc77_downEvt rc77_upEvt = 56 ∧ rc77_incCount rc77_upEvt rc77_downEvt = 56
      ∧ rc77_incCount rc77_downEvt rc77_downEvt = 48 ∧ rc77_incCount rc77_upEvt rc77_upEvt = 48) ∧
    
    (∀ A B : Finset (ConfigSpace (Fin 2)),
        rc77_isDownEvt A = true → rc77_isUpEvt B = true →
        2 ^ 2 * (rc75_disjOccF A B).card ≤ A.card * B.card) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨rc77_downUp_increases_fin2,
   rc77_downUp_count_fin2,
   ⟨rc77_all_dirs_fail_fin2.1, rc77_all_dirs_fail_fin2.2.2.1,
    rc77_all_dirs_fail_fin2.2.2.2.2.1, rc77_all_dirs_fail_fin2.2.2.2.2.2.2.1⟩,
   rc77_fixpoint_wall_fin2,
   rc77_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
