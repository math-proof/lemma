/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc77configmeasure.Part4
import Mathlib.Combinatorics.Hall.Basic
import Instance.StatisticalMechanics.Code.Walls.rc78hallmarriage
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


set_option maxRecDepth 8000 in


theorem rc78_perOrbitDom_rc72_witness : rc78_PerOrbitDom rc75_wA rc75_wB := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in 


theorem rc78_perOrbitDom_fin2 : ∀ A B : Finset (ConfigSpace (Fin 2)), rc78_PerOrbitDom A B := by
  decide

set_option maxRecDepth 8000 in


theorem rc78_topOrbit_card_fin2 :
    (rc78_srcOrbit rc75_wA rc75_wB (fun _ => (false, true))).card = 2
    ∧ (rc78_tgtOrbit rc75_wA rc75_wB (fun _ => (false, true))).card = 2 := by
  refine ⟨?_, ?_⟩ <;> decide


end StatMech.Walls
