/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc62twin.Part2
import Theorem.StatisticalMechanics.Code.Walls.menger_core.Part3
import Def.StatisticalMechanics.Code.Walls.gc63reroute
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
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set adjStep degK)

open Classical


theorem gc63b_refut_univ_sources :
    sources gc63b_refutEnds (univ : Finset (Fin 7)) = ({0, 1, 2, 3} : Finset (Fin 5)) := by decide


theorem gc63b_refut_K_sources :
    sources gc63b_refutEnds ({0} : Finset (Fin 7)) = ({0, 1} : Finset (Fin 5)) := by decide


theorem gc63b_refut_V_sources :
    sources gc63b_refutEnds ((univ : Finset (Fin 7)) \ ({0} : Finset (Fin 7)))
      = ({2, 3} : Finset (Fin 5)) := by decide


theorem gc63b_refut_loopless : ∀ i : Fin 7, ¬ (gc63b_refutEnds i).IsDiag := by decide


theorem gc63b_conn_1234 :
    connK gc63b_refutEnds (({0} : Finset (Fin 7)) ∪ ({1, 2, 3, 4} : Finset (Fin 7))) 1 3 :=
  Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩


theorem gc63b_conn_1256 :
    connK gc63b_refutEnds (({0} : Finset (Fin 7)) ∪ ({1, 2, 5, 6} : Finset (Fin 7))) 1 3 :=
  (Relation.ReflTransGen.single (b := (0 : Fin 5)) ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨2, by decide, by decide, by decide, by decide⟩


theorem gc63b_conn_3456 :
    connK gc63b_refutEnds (({0} : Finset (Fin 7)) ∪ ({3, 4, 5, 6} : Finset (Fin 7))) 1 3 :=
  Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩


theorem gc63b_not_conn_empty :
    ¬ connK gc63b_refutEnds (({0} : Finset (Fin 7)) ∪ (∅ : Finset (Fin 7))) 1 3 := by
  rw [Finset.union_empty]
  intro h
  have inv : ∀ w : Fin 5, connK gc63b_refutEnds ({0} : Finset (Fin 7)) 1 w → (w = 0 ∨ w = 1) := by
    intro w hw
    induction hw with
    | refl => decide
    | @tail b c _ hstep ih =>
      obtain ⟨i, hi, hbi, hci, hbc⟩ := hstep
      rcases ih with rfl | rfl <;> (fin_cases hi <;> revert hbc hbi hci <;> revert c <;> decide)
  rcases inv 3 h with h3 | h3 <;> exact absurd h3 (by decide)


theorem gc63b_refut_LblockSet :
    gc51_LblockSet gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 3
      = ({{1, 2, 3, 4}, {1, 2, 5, 6}, {3, 4, 5, 6}} : Finset (Finset (Fin 7))) := by
  rw [gc51_LblockSet]
  have hV : (univ : Finset (Fin 7)) \ ({0} : Finset (Fin 7)) = ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by
    decide
  rw [hV]
  have hset : ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)).powerset.filter
      (fun L => sources gc63b_refutEnds L = (∅ : Finset (Fin 5)))
      = ({∅, {1, 2, 3, 4}, {1, 2, 5, 6}, {3, 4, 5, 6}} : Finset (Finset (Fin 7))) := by decide
  rw [show ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)).powerset.filter
        (fun L => sources gc63b_refutEnds L = (∅ : Finset (Fin 5))
          ∧ connK gc63b_refutEnds (({0} : Finset (Fin 7)) ∪ L) 1 3)
      = (({1, 2, 3, 4, 5, 6} : Finset (Fin 7)).powerset.filter
          (fun L => sources gc63b_refutEnds L = (∅ : Finset (Fin 5)))).filter
            (fun L => connK gc63b_refutEnds (({0} : Finset (Fin 7)) ∪ L) 1 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  ext L
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hLmem, hconn⟩
    rcases hLmem with rfl | rfl | rfl | rfl
    · exact absurd hconn gc63b_not_conn_empty
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨by simp, gc63b_conn_1234⟩
    · exact ⟨by simp, gc63b_conn_1256⟩
    · exact ⟨by simp, gc63b_conn_3456⟩


theorem gc63b_not_conn_of_invariant (G : Finset (Fin 7)) {a b : Fin 5} (C : Fin 5 → Prop)
    [DecidablePred C] (hCa : C a) (hCb : ¬ C b)
    (hclosed : ∀ c d : Fin 5, C c → (∃ i ∈ G, c ∈ gc63b_refutEnds i ∧ d ∈ gc63b_refutEnds i ∧ c ≠ d) → C d) :
    ¬ connK gc63b_refutEnds G a b := by
  intro h
  have inv : ∀ w : Fin 5, connK gc63b_refutEnds G a w → C w := by
    intro w hw
    induction hw with
    | refl => exact hCa
    | @tail c d _ hstep ih => exact hclosed c d ih hstep
  exact hCb (inv b h)


theorem gc63b_iso_056_0 :
    ¬ connK gc63b_refutEnds ({0, 5, 6} : Finset (Fin 7)) 0 2
    ∧ ¬ connK gc63b_refutEnds ({0, 5, 6} : Finset (Fin 7)) 0 3 := by
  refine ⟨gc63b_not_conn_of_invariant _ (fun w => w = 0 ∨ w = 1) (by decide) (by decide) ?_,
          gc63b_not_conn_of_invariant _ (fun w => w = 0 ∨ w = 1) (by decide) (by decide) ?_⟩ <;>
  · intro c d hc ⟨i, hi, hci, hdi, hcd⟩
    rcases hc with rfl | rfl <;> (fin_cases hi <;> revert hcd hci hdi <;> revert d <;> decide)


theorem gc63b_iso_056_1 :
    ¬ connK gc63b_refutEnds ({0, 5, 6} : Finset (Fin 7)) 1 2
    ∧ ¬ connK gc63b_refutEnds ({0, 5, 6} : Finset (Fin 7)) 1 3 := by
  refine ⟨gc63b_not_conn_of_invariant _ (fun w => w = 0 ∨ w = 1) (by decide) (by decide) ?_,
          gc63b_not_conn_of_invariant _ (fun w => w = 0 ∨ w = 1) (by decide) (by decide) ?_⟩ <;>
  · intro c d hc ⟨i, hi, hci, hdi, hcd⟩
    rcases hc with rfl | rfl <;> (fin_cases hi <;> revert hcd hci hdi <;> revert d <;> decide)


theorem gc63b_iso_012_4 :
    ¬ connK gc63b_refutEnds ({0, 1, 2} : Finset (Fin 7)) 2 4
    ∧ ¬ connK gc63b_refutEnds ({0, 1, 2} : Finset (Fin 7)) 3 4 := by
  refine ⟨gc63b_not_conn_of_invariant _ (fun w => w ≠ 4) (by decide) (by decide) ?_,
          gc63b_not_conn_of_invariant _ (fun w => w ≠ 4) (by decide) (by decide) ?_⟩ <;>
  · intro c d hc ⟨i, hi, hci, hdi, hcd⟩
    revert hc hcd hci hdi; revert d; fin_cases hi <;> revert c <;> decide


theorem gc63b_iso_024_2 :
    ¬ connK gc63b_refutEnds ({0, 2, 4} : Finset (Fin 7)) 0 2
    ∧ ¬ connK gc63b_refutEnds ({0, 2, 4} : Finset (Fin 7)) 1 2 := by
  refine ⟨gc63b_not_conn_of_invariant _ (fun w => w ≠ 2) (by decide) (by decide) ?_,
          gc63b_not_conn_of_invariant _ (fun w => w ≠ 2) (by decide) (by decide) ?_⟩ <;>
  · intro c d hc ⟨i, hi, hci, hdi, hcd⟩
    revert hc hcd hci hdi; revert d; fin_cases hi <;> revert c <;> decide


theorem gc63b_connector_cases {D : Finset (Fin 7)}
    (hDV : D ⊆ (univ : Finset (Fin 7)) \ ({0} : Finset (Fin 7)))
    (hDsrc : sources gc63b_refutEnds D = ({2, 3} : Finset (Fin 5))) :
    D = ({1, 2} : Finset (Fin 7)) ∨ D = ({3, 4} : Finset (Fin 7))
      ∨ D = ({5, 6} : Finset (Fin 7)) ∨ D = ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by
  have hVeq : (univ : Finset (Fin 7)) \ ({0} : Finset (Fin 7)) = ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by
    decide
  rw [hVeq] at hDV
  
  revert hDsrc
  have : ∀ D' ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)).powerset,
      sources gc63b_refutEnds D' = ({2, 3} : Finset (Fin 5)) →
        D' = ({1, 2} : Finset (Fin 7)) ∨ D' = ({3, 4} : Finset (Fin 7))
          ∨ D' = ({5, 6} : Finset (Fin 7)) ∨ D' = ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
  exact this D (Finset.mem_powerset.2 hDV)


theorem gc63b_rerouteConnector_false :
    ¬ gc59_RerouteConnector gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3 := by
  rintro ⟨D, hDV, hDsrc, hL⟩
  
  have hmem : ∀ L : Finset (Fin 7),
      L = ({1, 2, 3, 4} : Finset (Fin 7)) ∨ L = ({1, 2, 5, 6} : Finset (Fin 7))
        ∨ L = ({3, 4, 5, 6} : Finset (Fin 7)) →
      L ∈ gc51_LblockSet gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 3 := by
    intro L hLc; rw [gc63b_refut_LblockSet]; rcases hLc with rfl | rfl | rfl <;> decide
  
  
  have contra : ∀ (L : Finset (Fin 7)) (ia ib : Fin 7) (pa qa pb qb : Fin 5),
      L ∈ gc51_LblockSet gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 3 →
        gc63b_refutEnds ia = s(pa, qa) → gc63b_refutEnds ib = s(pb, qb) →
        ia ≠ ib →
        ia ∈ D ∩ (({0} : Finset (Fin 7)) ∪ L) → ib ∈ D ∩ (({0} : Finset (Fin 7)) ∪ L) →
        ¬ connK gc63b_refutEnds ((({0} : Finset (Fin 7)) ∪ L) \ {ia, ib}) pa qa →
        ¬ connK gc63b_refutEnds ((({0} : Finset (Fin 7)) ∪ L) \ {ia, ib}) pb qb →
        False := by
    intro L ia ib pa qa pb qb hLmem hia hib hiab hiaD hibD hna hnb
    obtain ⟨ds, hds, hpeel, _⟩ := hL L hLmem
    have haF : ia ∈ ds.toFinset := by rw [hds]; exact hiaD
    have hbF : ib ∈ ds.toFinset := by rw [hds]; exact hibD
    rcases gc63b_peel_reconn_pair gc63b_refutEnds ds _ hpeel ia ib haF hbF hiab hia hib with h | h
    · exact hna h
    · exact hnb h
  
  rcases gc63b_connector_cases hDV hDsrc with rfl | rfl | rfl | rfl
  · 
    refine contra ({1, 2, 5, 6} : Finset (Fin 7)) 1 2 0 2 0 3
      (hmem _ (Or.inr (Or.inl rfl))) (by decide) (by decide) (by decide)
      (by decide) (by decide) ?_ ?_
    · rw [show (({0} : Finset (Fin 7)) ∪ ({1, 2, 5, 6} : Finset (Fin 7))) \ ({1, 2} : Finset (Fin 7))
          = ({0, 5, 6} : Finset (Fin 7)) from by decide]
      exact gc63b_iso_056_0.1
    · rw [show (({0} : Finset (Fin 7)) ∪ ({1, 2, 5, 6} : Finset (Fin 7))) \ ({1, 2} : Finset (Fin 7))
          = ({0, 5, 6} : Finset (Fin 7)) from by decide]
      exact gc63b_iso_056_0.2
  · 
    refine contra ({3, 4, 5, 6} : Finset (Fin 7)) 3 4 1 2 1 3
      (hmem _ (Or.inr (Or.inr rfl))) (by decide) (by decide) (by decide)
      (by decide) (by decide) ?_ ?_
    · rw [show (({0} : Finset (Fin 7)) ∪ ({3, 4, 5, 6} : Finset (Fin 7))) \ ({3, 4} : Finset (Fin 7))
          = ({0, 5, 6} : Finset (Fin 7)) from by decide]
      exact gc63b_iso_056_1.1
    · rw [show (({0} : Finset (Fin 7)) ∪ ({3, 4, 5, 6} : Finset (Fin 7))) \ ({3, 4} : Finset (Fin 7))
          = ({0, 5, 6} : Finset (Fin 7)) from by decide]
      exact gc63b_iso_056_1.2
  · 
    refine contra ({1, 2, 5, 6} : Finset (Fin 7)) 5 6 2 4 3 4
      (hmem _ (Or.inr (Or.inl rfl))) (by decide) (by decide) (by decide)
      (by decide) (by decide) ?_ ?_
    · rw [show (({0} : Finset (Fin 7)) ∪ ({1, 2, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))
          = ({0, 1, 2} : Finset (Fin 7)) from by decide]
      exact gc63b_iso_012_4.1
    · rw [show (({0} : Finset (Fin 7)) ∪ ({1, 2, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))
          = ({0, 1, 2} : Finset (Fin 7)) from by decide]
      exact gc63b_iso_012_4.2
  · 
    refine contra ({1, 2, 3, 4} : Finset (Fin 7)) 1 3 0 2 1 2
      (hmem _ (Or.inl rfl)) (by decide) (by decide) (by decide)
      (by decide) (by decide) ?_ ?_
    · rw [show (({0} : Finset (Fin 7)) ∪ ({1, 2, 3, 4} : Finset (Fin 7))) \ ({1, 3} : Finset (Fin 7))
          = ({0, 2, 4} : Finset (Fin 7)) from by decide]
      exact gc63b_iso_024_2.1
    · rw [show (({0} : Finset (Fin 7)) ∪ ({1, 2, 3, 4} : Finset (Fin 7))) \ ({1, 3} : Finset (Fin 7))
          = ({0, 2, 4} : Finset (Fin 7)) from by decide]
      exact gc63b_iso_024_2.2


theorem gc63b_D56_sources :
    sources gc63b_refutEnds ({5, 6} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5)) := by decide


theorem gc63b_sem_1234 :
    connK gc63b_refutEnds ((({0} : Finset (Fin 7)) ∪ ({1, 2, 3, 4} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 1 3 := by
  rw [show (({0} : Finset (Fin 7)) ∪ ({1, 2, 3, 4} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))
      = ({0, 1, 2, 3, 4} : Finset (Fin 7)) from by decide]
  exact Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩


theorem gc63b_sem_1256 :
    connK gc63b_refutEnds ((({0} : Finset (Fin 7)) ∪ ({1, 2, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 1 3 := by
  rw [show (({0} : Finset (Fin 7)) ∪ ({1, 2, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))
      = ({0, 1, 2} : Finset (Fin 7)) from by decide]
  exact (Relation.ReflTransGen.single (b := (0 : Fin 5)) ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨2, by decide, by decide, by decide, by decide⟩


theorem gc63b_sem_3456 :
    connK gc63b_refutEnds ((({0} : Finset (Fin 7)) ∪ ({3, 4, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 1 3 := by
  rw [show (({0} : Finset (Fin 7)) ∪ ({3, 4, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))
      = ({0, 3, 4} : Finset (Fin 7)) from by decide]
  exact Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩


theorem gc63b_refut_disjointConnector :
    gc57_DisjointConnector gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3 := by
  refine ⟨({5, 6} : Finset (Fin 7)), ?_, gc63b_D56_sources, ?_⟩
  · rw [show (univ : Finset (Fin 7)) \ ({0} : Finset (Fin 7)) = ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)) from by decide]
    decide
  · intro L hL
    rw [gc63b_refut_LblockSet] at hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    
    have hdisj : ∀ (L' : Finset (Fin 7)),
        Disjoint ((({0} : Finset (Fin 7)) ∪ L') \ ({5, 6} : Finset (Fin 7))) ({5, 6} : Finset (Fin 7)) := by
      intro L'
      rw [Finset.disjoint_left]
      intro i hi hiD
      exact (Finset.mem_sdiff.1 hi).2 hiD
    have hsub : ∀ (L' : Finset (Fin 7)),
        (({0} : Finset (Fin 7)) ∪ L') \ ({5, 6} : Finset (Fin 7)) ⊆ ({0} : Finset (Fin 7)) ∪ L' :=
      fun L' => Finset.sdiff_subset
    rcases hL with rfl | rfl | rfl
    · exact ⟨_, hsub _, hdisj _, gc63b_sem_1234⟩
    · exact ⟨_, hsub _, hdisj _, gc63b_sem_1256⟩
    · exact ⟨_, hsub _, hdisj _, gc63b_sem_3456⟩


theorem gc63b_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (ds : List ι) (H : Finset ι), gc59_Peelable ends H ds →
        ∀ (a b : ι), a ∈ ds.toFinset → b ∈ ds.toFinset → a ≠ b →
          ∀ {pa qa pb qb : W}, ends a = s(pa, qa) → ends b = s(pb, qb) →
            connK ends (H \ {a, b}) pa qa ∨ connK ends (H \ {a, b}) pb qb)
    ∧ 
    (¬ gc59_RerouteConnector gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3)
    ∧ 
    gc57_DisjointConnector gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3 :=
  ⟨by
      intro ι W _ _ _ _ ends ds H hpeel a b ha hb hab pa qa pb qb hpa hpb
      exact gc63b_peel_reconn_pair ends ds H hpeel a b ha hb hab hpa hpb,
    gc63b_rerouteConnector_false,
    gc63b_refut_disjointConnector⟩

end StatMech.Walls
