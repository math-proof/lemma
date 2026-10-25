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
import Def.StatisticalMechanics.Code.Walls.gc61parallelg.Part3
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


theorem gc61_parWit_loopless : ∀ k : Fin 2, ¬ (gc61_parWit k).IsDiag := by decide


theorem gc61_parWit_two_disjoint :
    ∃ P₁ P₂ : Finset (Fin 2), P₁ ⊆ ({0, 1} : Finset (Fin 2)) ∧ P₂ ⊆ ({0, 1} : Finset (Fin 2)) ∧
      Disjoint P₁ P₂ ∧ sources gc61_parWit P₁ = ({0, 3} : Finset (Fin 4)) ∧
      sources gc61_parWit P₂ = ({0, 3} : Finset (Fin 4)) ∧
      connK gc61_parWit P₁ 0 3 ∧ connK gc61_parWit P₂ 0 3 :=
  gc61_two_disjoint_of_parallel gc61_parWit gc61_parWit_loopless (by decide) (by decide)
    (by decide) (by decide)


theorem gc61_witness_parallelTwin :
    gc61_ParallelTwinPresent gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
  refine ⟨({1, 2} : Finset (Fin 5)), 2, 0, ?_, gc59_witnessEnds_D_sources, by decide, by decide, ?_⟩
  · rw [show (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) from by decide]
    decide
  · intro L hL
    rw [gc59_witness_LblockSet] at hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl
    · 
      refine ⟨gc59_witness_conn_23, Or.inl ⟨by decide, by decide, ?_⟩⟩
      rw [show (({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({2} : Finset (Fin 5))
            = ({0, 3} : Finset (Fin 5)) from by decide]
      exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
    · 
      refine ⟨gc59_witness_conn_24, Or.inl ⟨by decide, by decide, ?_⟩⟩
      rw [show (({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) \ ({2} : Finset (Fin 5))
            = ({0, 4} : Finset (Fin 5)) from by decide]
      exact Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩
    · 
      exact ⟨gc59_witness_conn_34, Or.inr (by decide)⟩


theorem gc61_witness_disjointConnector :
    gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  gc61_disjointConnector_of_parallelTwin gc59_witnessEnds _ gc61_witness_parallelTwin


theorem gc61_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (i j : ι) (v g : W), i ≠ j → v ≠ g →
        ends i = s(v, g) → ends j = s(v, g) →
        ∀ P₁ : Finset ι, P₁ ⊆ ({i, j} : Finset ι) →
          sources ends P₁ = ({v, g} : Finset W) → connK ends (({i, j} : Finset ι) \ P₁) v g)
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W),
        gc61_ParallelTwinPresent ends K o x y g → gc57_DisjointConnector ends K o x y g)
    ∧ 
    (∃ (ends : Fin 3 → Sym2 (Fin 4)) (P₁ : Finset (Fin 3)),
      3 ≤ degK ends (univ : Finset (Fin 3)) (3 : Fin 4)
      ∧ connK ends (univ : Finset (Fin 3)) 1 3
      ∧ sources ends P₁ = ({1, 3} : Finset (Fin 4))
      ∧ ¬ connK ends ((univ : Finset (Fin 3)) \ P₁) 1 3)
    ∧ 
    gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  ⟨fun ends i j v g hij hvg hi hj P₁ hP₁G hP₁src =>
      gc61_relative2conn_of_parallel ends hij hvg hi hj P₁ hP₁G hP₁src,
    fun ends K o x y g h => gc61_disjointConnector_of_parallelTwin ends K h,
    ⟨gc61_gStar, {1}, by rw [gc61_gStar_gDeg], gc61_gStar_xg_conn, gc61_gStar_P1_sources,
      by rw [gc61_gStar_delete_eq]; exact gc61_gStar_delete_disconn⟩,
    gc61_witness_disjointConnector⟩

end StatMech.Walls
