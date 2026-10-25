/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc44flow.Part2
import Def.StatisticalMechanics.Code.Walls.gc45cycle.Part4
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  exists_conn_set sources_symmDiff path_exists mem_sources)

theorem gc45_diamondEnds_loopless : ∀ i : Fin 4, ¬ (gc45_diamondEnds i).IsDiag := by decide


theorem gc45_diamondEnds_univ_sources :
    sources gc45_diamondEnds (univ : Finset (Fin 4)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide


theorem gc45_diamond_evenSub_univ :
    gc45_evenSub gc45_diamondEnds (univ : Finset (Fin 4))
      = {(∅ : Finset (Fin 4)), ({0, 3} : Finset (Fin 4))} := by decide


theorem gc45_diamond_E_univ_eq_two :
    gc40_E gc45_diamondEnds (univ : Finset (Fin 4)) = 2 :=
  gc45_E_eq_two_of_nullity_one gc45_diamondEnds (univ : Finset (Fin 4))
    (by decide : ({0, 3} : Finset (Fin 4)) ≠ (∅ : Finset (Fin 4)))
    gc45_diamond_evenSub_univ


theorem gc45_diamond_not_forest : ¬ gc44_ForestHyp gc45_diamondEnds := by
  intro hforest
  have h := hforest (univ : Finset (Fin 4))
  rw [gc45_diamond_E_univ_eq_two] at h
  exact absurd h (by decide)


theorem gc45_diamond_Lset :
    gc43_Lset gc45_diamondEnds (0 : Fin 4) 1 2 3
      = {({0, 1} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4))} := by
  rw [gc43_Lset, ← Finset.filter_filter]
  rw [show ((univ : Finset (Fin 4)).powerset.filter
        (fun M => sources gc45_diamondEnds M = ({0, 1} : Finset (Fin 4))))
      = {({0, 1} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4))} from by decide]
  
  have h01 : connK gc45_diamondEnds ({0, 1} : Finset (Fin 4)) (1 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩
  have h13 : connK gc45_diamondEnds ({1, 3} : Finset (Fin 4)) (1 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩
  rw [Finset.filter_insert, Finset.filter_singleton, if_pos h01, if_pos h13]


theorem gc45_diamond_reach_12_subset {v : Fin 4}
    (h : connK gc45_diamondEnds ({1, 2} : Finset (Fin 4)) (0 : Fin 4) v) :
    v ∈ ({0, 2} : Finset (Fin 4)) := by
  induction h with
  | refl => decide
  | tail _ hstep ih =>
    obtain ⟨i, hi, ha, hb, hne⟩ := hstep
    
    
    
    fin_cases hi <;>
      simp only [gc45_diamondEnds, Matrix.cons_val_one, Matrix.cons_val_zero,
        Sym2.mem_iff, Matrix.cons_val] at ha hb ⊢ <;>
      rw [Finset.mem_insert, Finset.mem_singleton] at ih ⊢ <;>
      omega


theorem gc45_diamond_not_conn_12_01 :
    ¬ connK gc45_diamondEnds ({1, 2} : Finset (Fin 4)) (0 : Fin 4) (1 : Fin 4) := by
  intro h
  have := gc45_diamond_reach_12_subset h
  revert this; decide


theorem gc45_diamond_Rset :
    gc43_Rset gc45_diamondEnds (0 : Fin 4) 1 2 3 = {(univ : Finset (Fin 4))} := by
  rw [gc43_Rset, ← Finset.filter_filter]
  
  rw [show ((univ : Finset (Fin 4)).powerset.filter
        (fun M => sources gc45_diamondEnds M = ({0, 1, 2, 3} : Finset (Fin 4))))
      = {({1, 2} : Finset (Fin 4)), (univ : Finset (Fin 4))} from by decide]
  
  have hox : connK gc45_diamondEnds (univ : Finset (Fin 4)) (0 : Fin 4) (1 : Fin 4) :=
    Relation.ReflTransGen.head (b := (3 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩)
  have hoy : connK gc45_diamondEnds (univ : Finset (Fin 4)) (0 : Fin 4) (2 : Fin 4) :=
    Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩
  have hog : connK gc45_diamondEnds (univ : Finset (Fin 4)) (0 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩
  
  have hng : ¬ (connK gc45_diamondEnds ({1, 2} : Finset (Fin 4)) (0 : Fin 4) (1 : Fin 4)
      ∧ connK gc45_diamondEnds ({1, 2} : Finset (Fin 4)) (0 : Fin 4) (2 : Fin 4)
      ∧ connK gc45_diamondEnds ({1, 2} : Finset (Fin 4)) (0 : Fin 4) (3 : Fin 4)) := by
    rintro ⟨h01, _, _⟩
    exact gc45_diamond_not_conn_12_01 h01
  rw [Finset.filter_insert, if_neg hng, Finset.filter_singleton, if_pos ⟨hox, hoy, hog⟩]


theorem gc45_diamond_TreeLHS : gc45_TreeLHS gc45_diamondEnds (0 : Fin 4) 1 2 3 := by
  intro M hM
  rw [gc45_diamond_Lset, Finset.mem_insert, Finset.mem_singleton] at hM
  rcases hM with h | h <;> subst h <;> decide


theorem gc45_diamond_NullityOneRelocation :
    gc45_NullityOneRelocation gc45_diamondEnds (0 : Fin 4) 1 2 3 := by
  refine ⟨fun _ => (univ : Finset (Fin 4)), ?_, ?_⟩
  · intro M hM
    rw [gc45_diamond_Rset, Finset.mem_singleton]
  · intro M' hM'
    rw [gc45_diamond_Rset, Finset.mem_singleton] at hM'
    subst hM'
    rw [gc45_diamond_Lset]
    
    rw [show ({({0, 1} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4))} : Finset (Finset (Fin 4))).filter
          (fun M => (univ : Finset (Fin 4)) = (univ : Finset (Fin 4)))
        = {({0, 1} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4))} from by decide]
    rw [gc45_diamond_E_univ_eq_two]
    decide


theorem gc45_diamond_core : gc39_ThreeColouringCountIneq gc45_diamondEnds (0 : Fin 4) 1 2 3 :=
  gc45_countIneq_of_nullityOneReloc gc45_diamondEnds gc45_diamondEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc45_diamondEnds_univ_sources gc45_diamond_TreeLHS gc45_diamond_NullityOneRelocation


theorem gc45_diamond_EMassResidue : gc42_EMassResidue gc45_diamondEnds (0 : Fin 4) 1 2 3 :=
  gc45_EMassResidue_of_nullityOneReloc gc45_diamondEnds (0 : Fin 4) 1 2 3
    gc45_diamond_TreeLHS gc45_diamond_NullityOneRelocation


theorem gc45_reloc_applies_diamond :
    (∀ i : Fin 4, ¬ (gc45_diamondEnds i).IsDiag)
      ∧ sources gc45_diamondEnds (univ : Finset (Fin 4)) = ({0, 1, 2, 3} : Finset (Fin 4))
      ∧ gc40_E gc45_diamondEnds (univ : Finset (Fin 4)) = 2
      ∧ gc45_TreeLHS gc45_diamondEnds (0 : Fin 4) 1 2 3
      ∧ gc45_NullityOneRelocation gc45_diamondEnds (0 : Fin 4) 1 2 3 :=
  ⟨gc45_diamondEnds_loopless, gc45_diamondEnds_univ_sources, gc45_diamond_E_univ_eq_two,
    gc45_diamond_TreeLHS, gc45_diamond_NullityOneRelocation⟩

end StatMech.Walls
