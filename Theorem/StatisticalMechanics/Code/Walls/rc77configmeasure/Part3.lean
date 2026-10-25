/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc77configmeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part7
import Def.StatisticalMechanics.Code.Walls.rc77configmeasure.Part3
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in


theorem rc77_all_dirs_fail_fin2 :
    
    rc77_incCount rc77_downEvt rc77_upEvt = 56 ∧ rc77_decCount rc77_downEvt rc77_upEvt = 0 ∧
    
    rc77_incCount rc77_upEvt rc77_downEvt = 56 ∧ rc77_decCount rc77_upEvt rc77_downEvt = 0 ∧
    
    rc77_incCount rc77_downEvt rc77_downEvt = 48 ∧ rc77_decCount rc77_downEvt rc77_downEvt = 8 ∧
    
    rc77_incCount rc77_upEvt rc77_upEvt = 48 ∧ rc77_decCount rc77_upEvt rc77_upEvt = 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide


end StatMech.Walls
