/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.menger_core.Part3
import Def.StatisticalMechanics.Code.Walls.menger_general.Part6
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

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm adjStep degK compOf
  sources_symmDiff mem_sources path_exists exists_conn_set)

open Classical


theorem mngg_test_cut_disconnects :
    ¬ connK mngg_theta ((univ : Finset (Fin 6)) \ mngg_theta_cut) 0 4 := by
  intro h
  have inv : ∀ w : Fin 5,
      connK mngg_theta ((univ : Finset (Fin 6)) \ mngg_theta_cut) 0 w → w = 0 := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hc, hd, hcd⟩ := hstep
      
      simp only [mngg_theta_cut, Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
      subst ih
      fin_cases i <;> simp_all [mngg_theta]
  exact absurd (inv 4 h) (by decide)


theorem mngg_test_maxflow_eq_mincut :
    mngg_IsCut mngg_theta (univ : Finset (Fin 6)) 0 4 mngg_theta_cut ∧
    #mngg_theta_cut = 3 := by
  refine ⟨⟨by decide, mngg_test_cut_disconnects⟩, by decide⟩


end StatMech.Walls
