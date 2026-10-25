/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc49nullity2.Part3
import Def.StatisticalMechanics.Code.Walls.gc50threereplica.Part2
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
  switching_card₂ connK_symm exists_conn_set sources_symmDiff path_exists mem_sources)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc50_EMassResidue_of_perKDom (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g)
    (h : gc50_PerKDom ends o x y g) :
    gc42_EMassResidue ends o x y g := by
  unfold gc42_EMassResidue
  rw [gc50_LHS_eq_perKsum ends hnd hox, gc50_RHS_eq_perKsum ends hnd hox hoy hog hxy hxg]
  exact Finset.sum_le_sum h


theorem gc50_EMassResidue_iff_perKsum (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) :
    gc42_EMassResidue ends o x y g
      ↔ (∑ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
            gc50_Lblock ends K o x g)
          ≤ ∑ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
              gc50_Rblock ends K o x y g := by
  unfold gc42_EMassResidue
  rw [gc50_LHS_eq_perKsum ends hnd hox, gc50_RHS_eq_perKsum ends hnd hox hoy hog hxy hxg]


theorem gc50_countIneq_of_perKDom (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : gc50_PerKDom ends o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc42_countIneq_of_EMass ends hnd hox hoy hog hxy hxg hyg huniv
    (gc50_EMassResidue_of_perKDom ends hnd hox hoy hog hxy hxg h)

end Abstract

open Classical


theorem gc50_witness_oxCurrents :
    (univ : Finset (Fin 4)).powerset.filter
        (fun K => sources gc49_witnessEnds K = ({0, 1} : Finset (Fin 4)))
      = {({1, 3} : Finset (Fin 4)), {2, 3}} := by decide


theorem gc50_witness_Lblock_K13 :
    gc50_Lblock gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 3 = 1 := by
  rw [gc50_Lblock]
  rw [show ((univ : Finset (Fin 4)) \ ({1, 3} : Finset (Fin 4))).powerset.filter
        (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4))
          ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ L) 1 3)
      = {(∅ : Finset (Fin 4))} from ?_]
  · decide
  · 
    have hV : (univ : Finset (Fin 4)) \ ({1, 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) := by
      decide
    rw [hV]
    have hset : ({0, 2} : Finset (Fin 4)).powerset.filter
        (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4)))
        = {(∅ : Finset (Fin 4))} := by decide
    rw [show ({0, 2} : Finset (Fin 4)).powerset.filter
          (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4))
            ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ L) 1 3)
        = (({0, 2} : Finset (Fin 4)).powerset.filter
            (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4)))).filter
              (fun L => connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ L) 1 3) from by
      rw [Finset.filter_filter]]
    rw [hset]
    have hconn : connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ (∅ : Finset (Fin 4))) 1 3 := by
      rw [Finset.union_empty]
      exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
    rw [Finset.filter_singleton, if_pos hconn]


theorem gc50_witness_univ_allConn :
    connK gc49_witnessEnds (univ : Finset (Fin 4)) 0 1
      ∧ connK gc49_witnessEnds (univ : Finset (Fin 4)) 0 2
      ∧ connK gc49_witnessEnds (univ : Finset (Fin 4)) 0 3 := by
  refine ⟨?_, ?_, ?_⟩
  · exact Relation.ReflTransGen.head (b := (3 : Fin 4))
      ⟨1, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩)
  · exact Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩
  · exact Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩


theorem gc50_witness_Rblock_K13 :
    gc50_Rblock gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 = 1 := by
  rw [gc50_Rblock]
  have hV : (univ : Finset (Fin 4)) \ ({1, 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) := by
    decide
  rw [hV]
  have hset : ({0, 2} : Finset (Fin 4)).powerset.filter
      (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4)))
      = {({0, 2} : Finset (Fin 4))} := by decide
  rw [show ({0, 2} : Finset (Fin 4)).powerset.filter
        (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4))
          ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 1
          ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 2
          ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 3)
      = (({0, 2} : Finset (Fin 4)).powerset.filter
          (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4)))).filter
            (fun Q => connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 1
              ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 2
              ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  have hunivEq : ({1, 3} : Finset (Fin 4)) ∪ ({0, 2} : Finset (Fin 4)) = (univ : Finset (Fin 4)) := by
    decide
  have hconn : connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ ({0, 2} : Finset (Fin 4))) 0 1
      ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ ({0, 2} : Finset (Fin 4))) 0 2
      ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ ({0, 2} : Finset (Fin 4))) 0 3 := by
    rw [hunivEq]; exact gc50_witness_univ_allConn
  rw [Finset.filter_singleton, if_pos hconn, Finset.card_singleton]


theorem gc50_witness_Lblock_K23 :
    gc50_Lblock gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 3 = 1 := by
  rw [gc50_Lblock]
  have hV : (univ : Finset (Fin 4)) \ ({2, 3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) := by
    decide
  rw [hV]
  have hset : ({0, 1} : Finset (Fin 4)).powerset.filter
      (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4)))
      = {(∅ : Finset (Fin 4))} := by decide
  rw [show ({0, 1} : Finset (Fin 4)).powerset.filter
        (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4))
          ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ L) 1 3)
      = (({0, 1} : Finset (Fin 4)).powerset.filter
          (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4)))).filter
            (fun L => connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ L) 1 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  have hconn : connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ (∅ : Finset (Fin 4))) 1 3 := by
    rw [Finset.union_empty]
    exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
  rw [Finset.filter_singleton, if_pos hconn, Finset.card_singleton]


theorem gc50_witness_Rblock_K23 :
    gc50_Rblock gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 = 1 := by
  rw [gc50_Rblock]
  have hV : (univ : Finset (Fin 4)) \ ({2, 3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) := by
    decide
  rw [hV]
  have hset : ({0, 1} : Finset (Fin 4)).powerset.filter
      (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4)))
      = {({0, 1} : Finset (Fin 4))} := by decide
  rw [show ({0, 1} : Finset (Fin 4)).powerset.filter
        (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4))
          ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 1
          ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 2
          ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 3)
      = (({0, 1} : Finset (Fin 4)).powerset.filter
          (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4)))).filter
            (fun Q => connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 1
              ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 2
              ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  have hunivEq : ({2, 3} : Finset (Fin 4)) ∪ ({0, 1} : Finset (Fin 4)) = (univ : Finset (Fin 4)) := by
    decide
  have hconn : connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ ({0, 1} : Finset (Fin 4))) 0 1
      ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ ({0, 1} : Finset (Fin 4))) 0 2
      ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ ({0, 1} : Finset (Fin 4))) 0 3 := by
    rw [hunivEq]; exact gc50_witness_univ_allConn
  rw [Finset.filter_singleton, if_pos hconn, Finset.card_singleton]


theorem gc50_witness_perKDom : gc50_PerKDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
  intro K hK
  rw [gc50_witness_oxCurrents] at hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hK
  rcases hK with rfl | rfl
  · rw [gc50_witness_Lblock_K13, gc50_witness_Rblock_K13]
  · rw [gc50_witness_Lblock_K23, gc50_witness_Rblock_K23]


theorem gc50_witness_EMassResidue_via_perK :
    gc42_EMassResidue gc49_witnessEnds (0 : Fin 4) 1 2 3 :=
  gc50_EMassResidue_of_perKDom gc49_witnessEnds gc49_witnessEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) gc50_witness_perKDom


theorem gc50_perK_succeeds_where_perN1_fails :
    gc50_PerKDom gc49_witnessEnds (0 : Fin 4) 1 2 3
      ∧ #(((univ : Finset (Fin 4)) \ ∅).powerset.filter
          (fun n₂ => sources gc49_witnessEnds n₂ = ({0, 1} : Finset (Fin 4))
            ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ n₂) 1 3))
        > #(((univ : Finset (Fin 4)) \ ∅).powerset.filter
            (fun m₂ => sources gc49_witnessEnds m₂ = ({0, 1, 2, 3} : Finset (Fin 4))
              ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 1
              ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 2
              ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 3)) :=
  ⟨gc50_witness_perKDom, gc49_perN1Dom_false⟩

end StatMech.Walls
