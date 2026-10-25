/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.menger_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc60exhaustive.Part2
import Def.StatisticalMechanics.Code.Walls.gc61parallelg.Part2
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
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set adjStep degK)

open Classical


theorem gc61_gStar_univ_sources :
    sources gc61_gStar (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide


theorem gc61_gStar_gDeg : degK gc61_gStar (univ : Finset (Fin 3)) (3 : Fin 4) = 3 := by decide


theorem gc61_gStar_xg_conn : connK gc61_gStar (univ : Finset (Fin 3)) 1 3 :=
  Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩


theorem gc61_gStar_P1_sources :
    sources gc61_gStar ({1} : Finset (Fin 3)) = ({1, 3} : Finset (Fin 4)) := by decide


theorem gc61_gStar_delete_eq :
    (univ : Finset (Fin 3)) \ ({1} : Finset (Fin 3)) = ({0, 2} : Finset (Fin 3)) := by decide


theorem gc61_gStar_delete_disconn :
    ¬ connK gc61_gStar ({0, 2} : Finset (Fin 3)) 1 3 := by
  intro h
  have inv : ∀ w : Fin 4, connK gc61_gStar ({0, 2} : Finset (Fin 3)) 1 w → w = 1 := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail b c _ hstep ih =>
      obtain ⟨i, hi, hbi, hci, hbc⟩ := hstep
      subst ih; fin_cases hi <;> revert hbc hbi hci <;> revert c <;> decide
  exact absurd (inv 3 h) (by decide)


theorem gc61_relative2conn_of_gDegGe3_false :
    ∃ (ends : Fin 3 → Sym2 (Fin 4)) (P₁ : Finset (Fin 3)),
      sources ends (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4))
      ∧ 3 ≤ degK ends (univ : Finset (Fin 3)) (3 : Fin 4)
      ∧ connK ends (univ : Finset (Fin 3)) 1 3
      ∧ P₁ ⊆ (univ : Finset (Fin 3))
      ∧ sources ends P₁ = ({1, 3} : Finset (Fin 4))
      ∧ ¬ connK ends ((univ : Finset (Fin 3)) \ P₁) 1 3 := by
  refine ⟨gc61_gStar, {1}, gc61_gStar_univ_sources, by rw [gc61_gStar_gDeg], gc61_gStar_xg_conn,
    Finset.subset_univ _, gc61_gStar_P1_sources, ?_⟩
  rw [gc61_gStar_delete_eq]; exact gc61_gStar_delete_disconn


theorem gc61_gStar_rel2_x_g_fails :
    ¬ (∀ P₁ : Finset (Fin 3), P₁ ⊆ (univ : Finset (Fin 3)) →
        sources gc61_gStar P₁ = ({1, 3} : Finset (Fin 4)) →
        connK gc61_gStar ((univ : Finset (Fin 3)) \ P₁) 1 3) := by
  intro h
  have := h {1} (Finset.subset_univ _) gc61_gStar_P1_sources
  rw [gc61_gStar_delete_eq] at this
  exact gc61_gStar_delete_disconn this


end StatMech.Walls
