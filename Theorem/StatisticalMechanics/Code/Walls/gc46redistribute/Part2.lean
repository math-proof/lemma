/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc46redistribute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc45cycle.Part4
import Def.StatisticalMechanics.Code.Walls.gc46redistribute
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

theorem gc46_defectEnds_loopless : ∀ i : Fin 5, ¬ (gc46_defectEnds i).IsDiag := by decide


theorem gc46_defectEnds_univ_sources :
    sources gc46_defectEnds (univ : Finset (Fin 5)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide


theorem gc46_defect_Lset :
    gc43_Lset gc46_defectEnds (0 : Fin 4) 1 2 3
      = {({3, 4} : Finset (Fin 5)), {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}} := by
  rw [gc43_Lset, ← Finset.filter_filter]
  rw [show ((univ : Finset (Fin 5)).powerset.filter
        (fun M => sources gc46_defectEnds M = ({0, 1} : Finset (Fin 4))))
      = {({3, 4} : Finset (Fin 5)), {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}} from by decide]
  
  have g1 : connK gc46_defectEnds ({3, 4} : Finset (Fin 5)) (1 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩
  have g2 : connK gc46_defectEnds ({0, 1, 3, 4} : Finset (Fin 5)) (1 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩
  have g3 : connK gc46_defectEnds ({0, 2, 3, 4} : Finset (Fin 5)) (1 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩
  have g4 : connK gc46_defectEnds ({1, 2, 3, 4} : Finset (Fin 5)) (1 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩
  rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton,
    if_pos g1, if_pos g2, if_pos g3, if_pos g4]


theorem gc46_defect_Rset :
    gc43_Rset gc46_defectEnds (0 : Fin 4) 1 2 3
      = {({0, 3, 4} : Finset (Fin 5)), {1, 3, 4}, {2, 3, 4}, univ} := by
  rw [gc43_Rset, ← Finset.filter_filter]
  rw [show ((univ : Finset (Fin 5)).powerset.filter
        (fun M => sources gc46_defectEnds M = ({0, 1, 2, 3} : Finset (Fin 4))))
      = {({0, 3, 4} : Finset (Fin 5)), {1, 3, 4}, {2, 3, 4}, univ} from by decide]
  
  
  have gate034 : connK gc46_defectEnds ({0, 3, 4} : Finset (Fin 5)) 0 1
      ∧ connK gc46_defectEnds ({0, 3, 4} : Finset (Fin 5)) 0 2
      ∧ connK gc46_defectEnds ({0, 3, 4} : Finset (Fin 5)) 0 3 := by
    refine ⟨?_, ?_, ?_⟩
    · exact Relation.ReflTransGen.head (b := (3 : Fin 4))
        ⟨3, by decide, by decide, by decide, by decide⟩
        (Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩)
    · exact Relation.ReflTransGen.head (b := (3 : Fin 4))
        ⟨3, by decide, by decide, by decide, by decide⟩
        (Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩)
    · exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
  have gate134 : connK gc46_defectEnds ({1, 3, 4} : Finset (Fin 5)) 0 1
      ∧ connK gc46_defectEnds ({1, 3, 4} : Finset (Fin 5)) 0 2
      ∧ connK gc46_defectEnds ({1, 3, 4} : Finset (Fin 5)) 0 3 := by
    refine ⟨?_, ?_, ?_⟩
    · exact Relation.ReflTransGen.head (b := (3 : Fin 4))
        ⟨3, by decide, by decide, by decide, by decide⟩
        (Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩)
    · exact Relation.ReflTransGen.head (b := (3 : Fin 4))
        ⟨3, by decide, by decide, by decide, by decide⟩
        (Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩)
    · exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
  have gate234 : connK gc46_defectEnds ({2, 3, 4} : Finset (Fin 5)) 0 1
      ∧ connK gc46_defectEnds ({2, 3, 4} : Finset (Fin 5)) 0 2
      ∧ connK gc46_defectEnds ({2, 3, 4} : Finset (Fin 5)) 0 3 := by
    refine ⟨?_, ?_, ?_⟩
    · exact Relation.ReflTransGen.head (b := (3 : Fin 4))
        ⟨3, by decide, by decide, by decide, by decide⟩
        (Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩)
    · exact Relation.ReflTransGen.head (b := (3 : Fin 4))
        ⟨3, by decide, by decide, by decide, by decide⟩
        (Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩)
    · exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
  have gateU : connK gc46_defectEnds (univ : Finset (Fin 5)) 0 1
      ∧ connK gc46_defectEnds (univ : Finset (Fin 5)) 0 2
      ∧ connK gc46_defectEnds (univ : Finset (Fin 5)) 0 3 := by
    refine ⟨?_, ?_, ?_⟩
    · exact Relation.ReflTransGen.head (b := (3 : Fin 4))
        ⟨3, by decide, by decide, by decide, by decide⟩
        (Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩)
    · exact Relation.ReflTransGen.head (b := (3 : Fin 4))
        ⟨3, by decide, by decide, by decide, by decide⟩
        (Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩)
    · exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
  rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton,
    if_pos gate034, if_pos gate134, if_pos gate234, if_pos gateU]


theorem gc46_defect_EMassResidue : gc42_EMassResidue gc46_defectEnds (0 : Fin 4) 1 2 3 := by
  unfold gc42_EMassResidue
  rw [gc43_LHS_eq_gatedSum, gc43_RHS_eq_gatedSum, gc46_defect_Lset, gc46_defect_Rset]
  
  have hL : (∑ M ∈ ({({3, 4} : Finset (Fin 5)), {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}} :
      Finset (Finset (Fin 5))), gc40_E gc46_defectEnds M) = 7 := by decide
  have hR : (∑ M ∈ ({({0, 3, 4} : Finset (Fin 5)), {1, 3, 4}, {2, 3, 4}, univ} :
      Finset (Finset (Fin 5))), gc40_E gc46_defectEnds M) = 7 := by decide
  rw [hL, hR]


theorem gc46_defect_not_FibreDomReloc :
    ¬ gc43_FibreDomReloc gc46_defectEnds (0 : Fin 4) 1 2 3 := by
  rintro ⟨φ, hmaps, hfib⟩
  
  have hmem : ∀ M ∈ ({({0, 1, 3, 4} : Finset (Fin 5)), {0, 2, 3, 4}, {1, 2, 3, 4}} :
      Finset (Finset (Fin 5))), M ∈ gc43_Lset gc46_defectEnds (0 : Fin 4) 1 2 3 := by
    intro M hM; rw [gc46_defect_Lset]
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hM
    rcases hM with h | h | h <;> subst h <;> decide
  
  have hE2 : ∀ M ∈ ({({0, 1, 3, 4} : Finset (Fin 5)), {0, 2, 3, 4}, {1, 2, 3, 4}} :
      Finset (Finset (Fin 5))), φ M = univ := by
    intro M hM
    have hφmem := hmaps M (hmem M hM)
    rw [gc46_defect_Rset, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hφmem
    
    
    have hEM : gc40_E gc46_defectEnds M = 2 := by
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hM
      rcases hM with h | h | h <;> subst h <;> decide
    rcases hφmem with h | h | h | h
    · exfalso
      have := hfib ({0, 3, 4} : Finset (Fin 5)) (by rw [gc46_defect_Rset]; decide)
      have hle : gc40_E gc46_defectEnds M ≤ 1 := by
        rw [show gc40_E gc46_defectEnds ({0, 3, 4} : Finset (Fin 5)) = 1 from by decide] at this
        calc gc40_E gc46_defectEnds M
            ≤ ∑ N ∈ (gc43_Lset gc46_defectEnds (0 : Fin 4) 1 2 3).filter
                (fun N => φ N = ({0, 3, 4} : Finset (Fin 5))), gc40_E gc46_defectEnds N :=
              Finset.single_le_sum (f := fun N => gc40_E gc46_defectEnds N)
                (fun _ _ => Nat.zero_le _)
                (by rw [Finset.mem_filter]; exact ⟨hmem M hM, h⟩)
          _ ≤ 1 := this
      omega
    · exfalso
      have := hfib ({1, 3, 4} : Finset (Fin 5)) (by rw [gc46_defect_Rset]; decide)
      have hle : gc40_E gc46_defectEnds M ≤ 1 := by
        rw [show gc40_E gc46_defectEnds ({1, 3, 4} : Finset (Fin 5)) = 1 from by decide] at this
        calc gc40_E gc46_defectEnds M
            ≤ ∑ N ∈ (gc43_Lset gc46_defectEnds (0 : Fin 4) 1 2 3).filter
                (fun N => φ N = ({1, 3, 4} : Finset (Fin 5))), gc40_E gc46_defectEnds N :=
              Finset.single_le_sum (f := fun N => gc40_E gc46_defectEnds N)
                (fun _ _ => Nat.zero_le _)
                (by rw [Finset.mem_filter]; exact ⟨hmem M hM, h⟩)
          _ ≤ 1 := this
      omega
    · exfalso
      have := hfib ({2, 3, 4} : Finset (Fin 5)) (by rw [gc46_defect_Rset]; decide)
      have hle : gc40_E gc46_defectEnds M ≤ 1 := by
        rw [show gc40_E gc46_defectEnds ({2, 3, 4} : Finset (Fin 5)) = 1 from by decide] at this
        calc gc40_E gc46_defectEnds M
            ≤ ∑ N ∈ (gc43_Lset gc46_defectEnds (0 : Fin 4) 1 2 3).filter
                (fun N => φ N = ({2, 3, 4} : Finset (Fin 5))), gc40_E gc46_defectEnds N :=
              Finset.single_le_sum (f := fun N => gc40_E gc46_defectEnds N)
                (fun _ _ => Nat.zero_le _)
                (by rw [Finset.mem_filter]; exact ⟨hmem M hM, h⟩)
          _ ≤ 1 := this
      omega
    · exact h
  
  have hunivbound := hfib (univ : Finset (Fin 5)) (by rw [gc46_defect_Rset]; decide)
  rw [show gc40_E gc46_defectEnds (univ : Finset (Fin 5)) = 4 from by decide] at hunivbound
  
  have hsub3 : ({({0, 1, 3, 4} : Finset (Fin 5)), {0, 2, 3, 4}, {1, 2, 3, 4}} :
      Finset (Finset (Fin 5)))
      ⊆ (gc43_Lset gc46_defectEnds (0 : Fin 4) 1 2 3).filter (fun N => φ N = univ) := by
    intro M hM
    rw [Finset.mem_filter]
    exact ⟨hmem M hM, hE2 M hM⟩
  have hmass : (6 : ℕ) ≤ ∑ N ∈ (gc43_Lset gc46_defectEnds (0 : Fin 4) 1 2 3).filter
      (fun N => φ N = univ), gc40_E gc46_defectEnds N := by
    calc (6 : ℕ)
        = ∑ N ∈ ({({0, 1, 3, 4} : Finset (Fin 5)), {0, 2, 3, 4}, {1, 2, 3, 4}} :
            Finset (Finset (Fin 5))), gc40_E gc46_defectEnds N := by decide
      _ ≤ ∑ N ∈ (gc43_Lset gc46_defectEnds (0 : Fin 4) 1 2 3).filter
            (fun N => φ N = univ), gc40_E gc46_defectEnds N :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub3 (fun _ _ _ => Nat.zero_le _)
  omega


theorem gc46_fibreDomReloc_strictly_stronger :
    gc42_EMassResidue gc46_defectEnds (0 : Fin 4) 1 2 3
      ∧ ¬ gc43_FibreDomReloc gc46_defectEnds (0 : Fin 4) 1 2 3 :=
  ⟨gc46_defect_EMassResidue, gc46_defect_not_FibreDomReloc⟩

end StatMech.Walls
