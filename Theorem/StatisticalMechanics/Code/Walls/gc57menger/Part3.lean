/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc56pathremoval.Part3
import Def.StatisticalMechanics.Code.Walls.gc57menger.Part2
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


theorem gc57_refEnds_univ_sources :
    sources gc57_refEnds (univ : Finset (Fin 7)) = ({0, 1, 2, 3} : Finset (Fin 5)) := by decide


theorem gc57_refEnds_K_sources :
    sources gc57_refEnds ({6} : Finset (Fin 7)) = ({0, 1} : Finset (Fin 5)) := by decide


theorem gc57_refEnds_D_sources :
    sources gc57_refEnds ({0, 3} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5))
    ∧ sources gc57_refEnds ({1, 2} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5)) := by
  refine ⟨by decide, by decide⟩


theorem gc57_ref_base_lex_eq :
    (({6} : Finset (Fin 7)) ∪ (({0, 1, 2, 3} : Finset (Fin 7)) \ ({0, 3} : Finset (Fin 7))))
      = ({1, 2, 6} : Finset (Fin 7)) := by decide


theorem gc57_ref_base_wk_eq :
    (({6} : Finset (Fin 7)) ∪ (({0, 1, 2, 3} : Finset (Fin 7)) \ ({1, 2} : Finset (Fin 7))))
      = ({0, 3, 6} : Finset (Fin 7)) := by decide


theorem gc57_ref_wk_survives :
    connK gc57_refEnds ({0, 3, 6} : Finset (Fin 7)) 1 3 :=
  Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩


theorem gc57_ref_lex_fails :
    ¬ connK gc57_refEnds ({1, 2, 6} : Finset (Fin 7)) 1 3 := by
  intro h
  have inv : ∀ w : Fin 5, connK gc57_refEnds ({1, 2, 6} : Finset (Fin 7)) 1 w →
      (w = 0 ∨ w = 1) := by
    intro w hw
    induction hw with
    | refl => decide
    | @tail b c _ hstep ih =>
      obtain ⟨i, hi, hbi, hci, hbc⟩ := hstep
      rcases ih with rfl | rfl <;>
        (fin_cases hi <;> revert hbc hbi hci <;> revert c <;> decide)
  rcases inv 3 h with h3 | h3 <;> exact absurd h3 (by decide)


theorem gc57_lexMinD_refuted :
    sources gc57_refEnds ({6} : Finset (Fin 7)) = ({0, 1} : Finset (Fin 5))
    ∧ sources gc57_refEnds ({0, 3} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5))
    ∧ sources gc57_refEnds ({1, 2} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5))
    ∧ ¬ connK gc57_refEnds
        (({6} : Finset (Fin 7)) ∪ (({0, 1, 2, 3} : Finset (Fin 7)) \ ({0, 3} : Finset (Fin 7)))) 1 3
    ∧ connK gc57_refEnds
        (({6} : Finset (Fin 7)) ∪ (({0, 1, 2, 3} : Finset (Fin 7)) \ ({1, 2} : Finset (Fin 7)))) 1 3 := by
  refine ⟨gc57_refEnds_K_sources, by decide, by decide, ?_, ?_⟩
  · rw [gc57_ref_base_lex_eq]; exact gc57_ref_lex_fails
  · rw [gc57_ref_base_wk_eq]; exact gc57_ref_wk_survives


theorem gc57_status :
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W),
      gc57_DisjointConnector ends K o x y g ↔ gc55_RemovalSurvival ends K o x y g)
    ∧ (¬ connK gc57_refEnds
        (({6} : Finset (Fin 7)) ∪ (({0, 1, 2, 3} : Finset (Fin 7)) \ ({0, 3} : Finset (Fin 7)))) 1 3)
    ∧ (connK gc57_refEnds
        (({6} : Finset (Fin 7)) ∪ (({0, 1, 2, 3} : Finset (Fin 7)) \ ({1, 2} : Finset (Fin 7)))) 1 3)
    ∧ gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3
    ∧ gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 :=
  ⟨fun ends K o x y g => gc57_disjointConnector_iff_removalSurvival_residue ends K,
    (by rw [gc57_ref_base_lex_eq]; exact gc57_ref_lex_fails),
    (by rw [gc57_ref_base_wk_eq]; exact gc57_ref_wk_survives),
    gc57_witness_cosetGateDom, gc57_witness_perKCount⟩

end StatMech.Walls
