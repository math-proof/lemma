/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc74doubledwall
import Def.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part8
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


set_option maxRecDepth 8000 in


theorem rc75_adaptive_succeeds_where_rc72_failed :
    rc75_existsAdaptivePlan rc75_wA rc75_wB := by decide

set_option maxRecDepth 8000 in


theorem rc75_disjOcc_wit_card : (rc75_disjOccF rc75_wA rc75_wB).card = 2 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in 


theorem rc75_adaptivePlan_fin2 :
    ∀ A B : Finset (ConfigSpace (Fin 2)),
      2 ^ 2 * (rc75_disjOccF A B).card ≤ A.card * B.card → rc75_existsAdaptivePlan A B := by
  decide

set_option maxRecDepth 8000 in


theorem rc75_order_dependence :
    rc75_existsPlanOrder [1, 0] (rc75_sourceF rc75_wA rc75_wB) (rc75_prodF rc75_wA rc75_wB)
    ∧ ¬ rc75_existsPlanOrder [0, 1] (rc75_sourceF rc75_wA rc75_wB) (rc75_prodF rc75_wA rc75_wB)
    ∧ rc75_existsPlanOrder [0, 1] (rc75_sourceF rc75_gA rc75_gB) (rc75_prodF rc75_gA rc75_gB)
    ∧ ¬ rc75_existsPlanOrder [1, 0] (rc75_sourceF rc75_gA rc75_gB) (rc75_prodF rc75_gA rc75_gB) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide


end StatMech.Walls
