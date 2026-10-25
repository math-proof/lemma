/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc77configmeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part7
import Def.StatisticalMechanics.Code.Walls.rc77configmeasure
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


set_option maxRecDepth 8000 in


theorem rc77_downUp_increases_fin2 :
    (rc75_disjOccF rc77_wA rc77_wB).card = 0
    ∧ (rc75_disjOccF (rc77_downEvt 1 rc77_wA) (rc77_upEvt 1 rc77_wB)).card = 1 := by
  refine ⟨?_, ?_⟩ <;> decide


end StatMech.Walls
