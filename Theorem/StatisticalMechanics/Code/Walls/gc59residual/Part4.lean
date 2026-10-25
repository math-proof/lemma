/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc58cyclespace
import Def.StatisticalMechanics.Code.Walls.gc59residual.Part3
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


theorem gc59_witnessEnds_univ_sources :
    sources gc59_witnessEnds (univ : Finset (Fin 5)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide


theorem gc59_witnessEnds_K_sources :
    sources gc59_witnessEnds ({0} : Finset (Fin 5)) = ({0, 1} : Finset (Fin 4)) := by decide


theorem gc59_witnessEnds_D_sources :
    sources gc59_witnessEnds ({1, 2} : Finset (Fin 5)) = ({2, 3} : Finset (Fin 4)) := by decide


theorem gc59_witnessEnds_loopless : ∀ i : Fin 5, ¬ (gc59_witnessEnds i).IsDiag := by decide


theorem gc59_witness_conn_23 :
    connK gc59_witnessEnds (({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) 1 3 :=
  (Relation.ReflTransGen.single (b := (0 : Fin 4)) ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨2, by decide, by decide, by decide, by decide⟩


theorem gc59_witness_conn_24 :
    connK gc59_witnessEnds (({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) 1 3 :=
  (Relation.ReflTransGen.single (b := (0 : Fin 4)) ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨2, by decide, by decide, by decide, by decide⟩


theorem gc59_witness_conn_34 :
    connK gc59_witnessEnds (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) 1 3 :=
  (Relation.ReflTransGen.single (b := (0 : Fin 4)) ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨3, by decide, by decide, by decide, by decide⟩


theorem gc59_witness_LblockSet :
    gc51_LblockSet gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 3
      = ({{2, 3}, {2, 4}, {3, 4}} : Finset (Finset (Fin 5))) := by
  rw [gc51_LblockSet]
  have hV : (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) := by
    decide
  rw [hV]
  have hset : ({1, 2, 3, 4} : Finset (Fin 5)).powerset.filter
      (fun L => sources gc59_witnessEnds L = (∅ : Finset (Fin 4)))
      = ({∅, {2, 3}, {2, 4}, {3, 4}} : Finset (Finset (Fin 5))) := by decide
  rw [show ({1, 2, 3, 4} : Finset (Fin 5)).powerset.filter
        (fun L => sources gc59_witnessEnds L = (∅ : Finset (Fin 4))
          ∧ connK gc59_witnessEnds (({0} : Finset (Fin 5)) ∪ L) 1 3)
      = (({1, 2, 3, 4} : Finset (Fin 5)).powerset.filter
          (fun L => sources gc59_witnessEnds L = (∅ : Finset (Fin 4)))).filter
            (fun L => connK gc59_witnessEnds (({0} : Finset (Fin 5)) ∪ L) 1 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  
  have hne : ¬ connK gc59_witnessEnds (({0} : Finset (Fin 5)) ∪ (∅ : Finset (Fin 5))) 1 3 := by
    rw [Finset.union_empty]
    intro h
    
    have inv : ∀ w : Fin 4, connK gc59_witnessEnds ({0} : Finset (Fin 5)) 1 w → (w = 0 ∨ w = 1) := by
      intro w hw
      induction hw with
      | refl => decide
      | @tail b c _ hstep ih =>
        obtain ⟨i, hi, hbi, hci, hbc⟩ := hstep
        rcases ih with rfl | rfl <;> (fin_cases hi <;> revert hbc hbi hci <;> revert c <;> decide)
    rcases inv 3 h with h3 | h3 <;> exact absurd h3 (by decide)
  
  ext L
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hLmem, hconn⟩
    rcases hLmem with rfl | rfl | rfl | rfl
    · exact absurd hconn hne
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨by simp, gc59_witness_conn_23⟩
    · exact ⟨by simp, gc59_witness_conn_24⟩
    · exact ⟨by simp, gc59_witness_conn_34⟩


theorem gc59_witness_reconn_23 :
    connK gc59_witnessEnds ((({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ {2}) 0 3 := by
  have h : (({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({2} : Finset (Fin 5))
      = ({0, 3} : Finset (Fin 5)) := by decide
  rw [h]
  exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩


theorem gc59_witness_reconn_24 :
    connK gc59_witnessEnds ((({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) \ {2}) 0 3 := by
  have h : (({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) \ ({2} : Finset (Fin 5))
      = ({0, 4} : Finset (Fin 5)) := by decide
  rw [h]
  exact Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩


theorem gc59_witness_rerouteConnector :
    gc59_RerouteConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
  refine ⟨({1, 2} : Finset (Fin 5)), ?_, gc59_witnessEnds_D_sources, ?_⟩
  · rw [show (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) from by decide]
    decide
  · intro L hL
    rw [gc59_witness_LblockSet] at hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl
    · 
      refine ⟨[2], by decide, ⟨by decide, ⟨0, 3, by decide, gc59_witness_reconn_23⟩, trivial⟩,
        gc59_witness_conn_23⟩
    · 
      refine ⟨[2], by decide, ⟨by decide, ⟨0, 3, by decide, gc59_witness_reconn_24⟩, trivial⟩,
        gc59_witness_conn_24⟩
    · 
      refine ⟨[], by decide, trivial, gc59_witness_conn_34⟩


theorem gc59_witness_disjointConnector :
    gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  gc59_disjointConnector_of_reroute gc59_witnessEnds _ gc59_witness_rerouteConnector


theorem gc59_status :
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (a b : W) (G : Finset ι) (ds : List ι),
        gc59_Peelable ends G ds → connK ends G a b → connK ends (G \ ds.toFinset) a b)
    ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W),
        gc59_RerouteConnector ends K o x y g → gc57_DisjointConnector ends K o x y g)
    ∧ gc59_RerouteConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3
    ∧ gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  ⟨fun ends a b G ds hp hab => gc59_connK_of_peelable_sdiff ends G ds hp hab,
    fun ends K o x y g h => gc59_disjointConnector_of_reroute ends K h,
    gc59_witness_rerouteConnector, gc59_witness_disjointConnector⟩

end StatMech.Walls
