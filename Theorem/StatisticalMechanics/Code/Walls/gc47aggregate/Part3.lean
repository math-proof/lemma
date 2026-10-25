/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc46redistribute.Part2
import Def.StatisticalMechanics.Code.Walls.gc47aggregate.Part3
open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  exists_conn_set sources_symmDiff path_exists mem_sources)

theorem gc47_defectΦ_mapsTo :
    ∀ p ∈ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3,
      gc47_defectΦ p ∈ gc47_RHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3 := by
  rw [gc47_LHSpairs, gc46_defect_Lset, gc47_RHSpairs, gc46_defect_Rset]; decide


theorem gc47_defectΦ_injOn :
    Set.InjOn gc47_defectΦ (gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3) := by
  intro a ha b hb hab
  have hdec : ∀ p ∈ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3,
      ∀ q ∈ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3,
        gc47_defectΦ p = gc47_defectΦ q → p = q := by
    rw [gc47_LHSpairs, gc46_defect_Lset]; decide
  exact hdec a ha b hb hab


theorem gc47_defect_pairInjection :
    gc47_PairInjection gc46_defectEnds (0 : Fin 4) 1 2 3 :=
  ⟨gc47_defectΦ, gc47_defectΦ_mapsTo, gc47_defectΦ_injOn⟩


theorem gc47_defect_EMassResidue_via_pairs :
    gc42_EMassResidue gc46_defectEnds (0 : Fin 4) 1 2 3 :=
  gc47_EMassResidue_of_pairInjection gc46_defectEnds (0 : Fin 4) 1 2 3 gc47_defect_pairInjection


end StatMech.Walls
