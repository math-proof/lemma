/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc77configmeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part7
import Def.StatisticalMechanics.Code.Walls.rc77configmeasure.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in


theorem rc77_downUp_count_fin2 :
    rc77_downUpIncreases = 56 ∧ rc77_downUpDecreases = 0 := by
  refine ⟨?_, ?_⟩ <;> decide


end StatMech.Walls
