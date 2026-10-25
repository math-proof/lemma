/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc55graham.Part2
import Def.StatisticalMechanics.Code.Walls.gc56pathremoval.Part2
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

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set adjStep degK)

open Classical


theorem gc56_refEnds_univ_sources :
    sources gc56_refEnds (univ : Finset (Fin 7)) = ({0, 1, 2, 3} : Finset (Fin 5)) := by decide


theorem gc56_refEnds_K_sources :
    sources gc56_refEnds ({2} : Finset (Fin 7)) = ({0, 1} : Finset (Fin 5)) := by decide


theorem gc56_ref_base_eq :
    (({2} : Finset (Fin 7)) ∪ (({0, 1, 4, 5} : Finset (Fin 7)) \ ({1, 4} : Finset (Fin 7))))
      = ({0, 2, 5} : Finset (Fin 7)) := by decide


theorem gc56_ref_removalSurvives :
    connK gc56_refEnds ({0, 2, 5} : Finset (Fin 7)) 1 3 :=
  Relation.ReflTransGen.single ⟨5, by decide, by decide, by decide, by decide⟩


theorem gc56_ref_noReconnect :
    ¬ connK gc56_refEnds ({0, 2, 5} : Finset (Fin 7)) 2 4 := by
  intro h
  have inv : ∀ w : Fin 5, connK gc56_refEnds ({0, 2, 5} : Finset (Fin 7)) 2 w →
      (w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3) := by
    intro w hw
    induction hw with
    | refl => decide
    | @tail b c _ hstep ih =>
      obtain ⟨i, hi, hbi, hci, hbc⟩ := hstep
      rcases ih with rfl | rfl | rfl | rfl <;>
        (fin_cases hi <;> revert hbc hbi hci <;> revert c <;> decide)
  rcases inv 4 h with h4 | h4 | h4 | h4 <;> exact absurd h4 (by decide)


theorem gc56_pathReconnect_refuted :
    sources gc56_refEnds ({2} : Finset (Fin 7)) = ({0, 1} : Finset (Fin 5))
    ∧ (1 : Fin 7) ∈ ({0, 1, 4, 5} : Finset (Fin 7)) ∩ ({1, 4} : Finset (Fin 7))
    ∧ gc56_refEnds 1 = s(2, 4)
    ∧ connK gc56_refEnds
        (({2} : Finset (Fin 7)) ∪ (({0, 1, 4, 5} : Finset (Fin 7)) \ ({1, 4} : Finset (Fin 7)))) 1 3
    ∧ ¬ connK gc56_refEnds
        (({2} : Finset (Fin 7)) ∪ (({0, 1, 4, 5} : Finset (Fin 7)) \ ({1, 4} : Finset (Fin 7)))) 2 4 := by
  refine ⟨gc56_refEnds_K_sources, by decide, by decide, ?_, ?_⟩
  · rw [gc56_ref_base_eq]; exact gc56_ref_removalSurvives
  · rw [gc56_ref_base_eq]; exact gc56_ref_noReconnect


theorem gc56_status :
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W),
      gc56_PathReconnect ends K o x y g → gc55_RemovalSurvival ends K o x y g)
    ∧ (¬ connK gc56_refEnds
        (({2} : Finset (Fin 7)) ∪ (({0, 1, 4, 5} : Finset (Fin 7)) \ ({1, 4} : Finset (Fin 7)))) 2 4)
    ∧ gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3
    ∧ gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 :=
  ⟨fun ends K o x y g h => gc56_removalSurvival_of_pathReconnect ends K h,
    (by rw [gc56_ref_base_eq]; exact gc56_ref_noReconnect),
    gc56_witness_cosetGateDom, gc56_witness_perKCount⟩

end StatMech.Walls
