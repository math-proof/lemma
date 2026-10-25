/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc48pairinject.Part2
import Def.StatisticalMechanics.Code.Walls.gc49nullity2.Part2
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

open Classical


theorem gc49_witnessEnds_loopless : ∀ i : Fin 4, ¬ (gc49_witnessEnds i).IsDiag := by decide


theorem gc49_witnessEnds_univ_sources :
    sources gc49_witnessEnds (univ : Finset (Fin 4)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide


theorem gc49_witness_Lset :
    gc43_Lset gc49_witnessEnds (0 : Fin 4) 1 2 3
      = {({1, 3} : Finset (Fin 4)), {2, 3}} := by
  rw [gc43_Lset, ← Finset.filter_filter]
  rw [show ((univ : Finset (Fin 4)).powerset.filter
        (fun M => sources gc49_witnessEnds M = ({0, 1} : Finset (Fin 4))))
      = {({1, 3} : Finset (Fin 4)), {2, 3}} from by decide]
  have g1 : connK gc49_witnessEnds ({1, 3} : Finset (Fin 4)) (1 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
  have g2 : connK gc49_witnessEnds ({2, 3} : Finset (Fin 4)) (1 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
  rw [Finset.filter_insert, Finset.filter_singleton, if_pos g1, if_pos g2]


theorem gc49_witness_Rset :
    gc43_Rset gc49_witnessEnds (0 : Fin 4) 1 2 3
      = {(univ : Finset (Fin 4))} := by
  rw [gc43_Rset, ← Finset.filter_filter]
  rw [show ((univ : Finset (Fin 4)).powerset.filter
        (fun M => sources gc49_witnessEnds M = ({0, 1, 2, 3} : Finset (Fin 4))))
      = {({0, 3} : Finset (Fin 4)), univ} from by decide]
  
  
  have gbad : ¬ (connK gc49_witnessEnds ({0, 3} : Finset (Fin 4)) 0 1
      ∧ connK gc49_witnessEnds ({0, 3} : Finset (Fin 4)) 0 2
      ∧ connK gc49_witnessEnds ({0, 3} : Finset (Fin 4)) 0 3) := by
    rintro ⟨h01, _, _⟩
    
    have col : ∀ v : Fin 4, connK gc49_witnessEnds ({0, 3} : Finset (Fin 4)) 0 v →
        (v = 0 ∨ v = 2) := by
      intro v hv
      induction hv with
      | refl => exact Or.inl rfl
      | @tail b c _ hstep ih =>
        obtain ⟨i, hi, hbi, hci, hbc⟩ := hstep
        
        rcases ih with rfl | rfl <;>
          (fin_cases hi <;> revert hbc hbi hci <;> revert c <;> decide)
    rcases col 1 h01 with h | h <;> exact absurd h (by decide)
  have gU : connK gc49_witnessEnds (univ : Finset (Fin 4)) 0 1
      ∧ connK gc49_witnessEnds (univ : Finset (Fin 4)) 0 2
      ∧ connK gc49_witnessEnds (univ : Finset (Fin 4)) 0 3 := by
    refine ⟨?_, ?_, ?_⟩
    · exact Relation.ReflTransGen.head (b := (3 : Fin 4))
        ⟨1, by decide, by decide, by decide, by decide⟩
        (Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩)
    · exact Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩
    · exact Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩
  rw [Finset.filter_insert, Finset.filter_singleton, if_neg gbad, if_pos gU]


theorem gc49_witness_EMassResidue : gc42_EMassResidue gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
  unfold gc42_EMassResidue
  rw [gc43_LHS_eq_gatedSum, gc43_RHS_eq_gatedSum, gc49_witness_Lset, gc49_witness_Rset]
  have hL : (∑ M ∈ ({({1, 3} : Finset (Fin 4)), {2, 3}} : Finset (Finset (Fin 4))),
      gc40_E gc49_witnessEnds M) = 2 := by decide
  have hR : (∑ M ∈ ({(univ : Finset (Fin 4))} : Finset (Finset (Fin 4))),
      gc40_E gc49_witnessEnds M) = 2 := by decide
  rw [hL, hR]


theorem gc49_witness_innerL_empty :
    #(((univ : Finset (Fin 4)) \ ∅).powerset.filter
        (fun n₂ => sources gc49_witnessEnds n₂ = ({0, 1} : Finset (Fin 4))
          ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ n₂) 1 3)) = 2 := by
  have hset : ((univ : Finset (Fin 4)) \ ∅).powerset.filter
      (fun n₂ => sources gc49_witnessEnds n₂ = ({0, 1} : Finset (Fin 4))
        ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ n₂) 1 3)
      = gc43_Lset gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
    rw [gc43_Lset]
    apply Finset.filter_congr
    intro M hM
    simp only [Finset.empty_union]
  rw [hset, gc49_witness_Lset]; decide


theorem gc49_witness_innerR_empty :
    #(((univ : Finset (Fin 4)) \ ∅).powerset.filter
        (fun m₂ => sources gc49_witnessEnds m₂ = ({0, 1, 2, 3} : Finset (Fin 4))
          ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 1
          ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 2
          ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 3)) = 1 := by
  have hset : ((univ : Finset (Fin 4)) \ ∅).powerset.filter
      (fun m₂ => sources gc49_witnessEnds m₂ = ({0, 1, 2, 3} : Finset (Fin 4))
        ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 1
        ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 2
        ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 3)
      = gc43_Rset gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
    rw [gc43_Rset]
    apply Finset.filter_congr
    intro M hM
    simp only [Finset.empty_union]
  rw [hset, gc49_witness_Rset]; decide


theorem gc49_perN1Dom_false :
    #(((univ : Finset (Fin 4)) \ ∅).powerset.filter
        (fun n₂ => sources gc49_witnessEnds n₂ = ({0, 1} : Finset (Fin 4))
          ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ n₂) 1 3))
      > #(((univ : Finset (Fin 4)) \ ∅).powerset.filter
          (fun m₂ => sources gc49_witnessEnds m₂ = ({0, 1, 2, 3} : Finset (Fin 4))
            ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 1
            ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 2
            ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 3)) := by
  rw [gc49_witness_innerL_empty, gc49_witness_innerR_empty]; norm_num


theorem gc49_residue_is_aggregate :
    gc42_EMassResidue gc49_witnessEnds (0 : Fin 4) 1 2 3
      ∧ #(((univ : Finset (Fin 4)) \ ∅).powerset.filter
          (fun n₂ => sources gc49_witnessEnds n₂ = ({0, 1} : Finset (Fin 4))
            ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ n₂) 1 3))
        > #(((univ : Finset (Fin 4)) \ ∅).powerset.filter
            (fun m₂ => sources gc49_witnessEnds m₂ = ({0, 1, 2, 3} : Finset (Fin 4))
              ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 1
              ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 2
              ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 3)) :=
  ⟨gc49_witness_EMassResidue, gc49_perN1Dom_false⟩


theorem gc49_diamond_conn_yg :
    connK gc45_diamondEnds (univ : Finset (Fin 4)) 2 3 :=
  Relation.ReflTransGen.head (b := (0 : Fin 4))
    ⟨2, by decide, by decide, by decide, by decide⟩
    (Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩)


theorem gc49_diamond_switching :
    #((univ : Finset (Fin 4)).powerset.filter
        (fun K => sources gc45_diamondEnds K = ({0, 1} : Finset (Fin 4))))
      = #((univ : Finset (Fin 4)).powerset.filter
          (fun K => sources gc45_diamondEnds K = ({0, 1, 2, 3} : Finset (Fin 4)))) := by
  have h := gc49_switching_ox_of_oxyg gc45_diamondEnds (univ : Finset (Fin 4))
    (fun i _ => gc45_diamondEnds_loopless i)
    (o := 0) (x := 1) (y := 2) (g := 3) gc45_diamondEnds_univ_sources
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [if_pos gc49_diamond_conn_yg] at h
  exact h


theorem gc49_diamond_innerDom :
    gc49_InnerDom gc45_diamondEnds (0 : Fin 4) 1 2 3 :=
  (gc49_innerDom_iff_EMassResidue gc45_diamondEnds (0 : Fin 4) 1 2 3).mpr gc45_diamond_EMassResidue


theorem gc49_diamond_countIneq :
    gc39_ThreeColouringCountIneq gc45_diamondEnds (0 : Fin 4) 1 2 3 :=
  gc49_countIneq_of_innerDom gc45_diamondEnds gc45_diamondEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc45_diamondEnds_univ_sources gc49_diamond_innerDom

end StatMech.Walls
