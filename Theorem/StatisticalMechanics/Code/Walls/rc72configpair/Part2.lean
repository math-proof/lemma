/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc71disjpreserving.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Def.StatisticalMechanics.Code.Walls.rc72configpair.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


set_option maxRecDepth 8000 in


theorem rc72_witness_counts :
    (rc72_disjOcc rc72_wA rc72_wB).card = 2
    ∧ rc72_wA.card * rc72_wB.card = 9
    ∧ (rc72_reachCells rc72_wA rc72_wB).card = 7 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

set_option maxRecDepth 8000 in


theorem rc72_graftSwap_reach_cap_fin2 :
    (rc72_reachCells rc72_wA rc72_wB).card
      < 2 ^ 2 * (rc72_disjOcc rc72_wA rc72_wB).card := by
  decide


end StatMech.Walls
