/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc73brelconn.Part2
import Def.StatisticalMechanics.Code.Walls.gc74bbridge
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
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set adjStep degK)

open Classical


theorem gc74b_brEnds2_loopless : ∀ i : Fin 5, ¬ (gc74b_brEnds2 i).IsDiag := by decide


theorem gc74b_brEnds2_univ_sources :
    sources gc74b_brEnds2 (univ : Finset (Fin 5)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide


theorem gc74b_brEnds2_K_sources :
    sources gc74b_brEnds2 ({0} : Finset (Fin 5)) = ({0, 1} : Finset (Fin 4)) := by decide


theorem gc74b_brEnds2_g_deg3 : degK gc74b_brEnds2 (univ : Finset (Fin 5)) 3 = 3 := by decide


theorem gc74b_brEnds2_L_sources :
    sources gc74b_brEnds2 ({1, 2, 3} : Finset (Fin 5)) = (∅ : Finset (Fin 4)) := by decide


theorem gc74b_brEnds2_gate :
    connK gc74b_brEnds2 (({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) 1 3 :=
  Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩


theorem gc74b_brEnds2_og_conn :
    connK gc74b_brEnds2 (({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) 0 3 :=
  (Relation.ReflTransGen.single (b := (1 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨2, by decide, by decide, by decide, by decide⟩


theorem gc74b_brEnds2_bridge_cut :
    ¬ connK gc74b_brEnds2
      ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({0} : Finset (Fin 5))) 0 3 := by
  rw [show (({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({0} : Finset (Fin 5))
        = ({1, 2, 3} : Finset (Fin 5)) from by decide]
  intro h
  
  have inv : ∀ w : Fin 4, connK gc74b_brEnds2 ({1, 2, 3} : Finset (Fin 5)) 0 w → w = 0 := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hci, hdi, hcd⟩ := hstep
      subst ih
      fin_cases hi <;> revert hcd hci hdi <;> revert d <;> decide
  exact absurd (inv 3 h) (by decide)


theorem gc74b_bridge_edge_in_K :
    connK gc74b_brEnds2 (({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) 0 3
      ∧ (¬ connK gc74b_brEnds2
          ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({0} : Finset (Fin 5))) 0 3)
      ∧ (0 : Fin 5) ∈ ({0} : Finset (Fin 5)) :=
  ⟨gc74b_brEnds2_og_conn, gc74b_brEnds2_bridge_cut, by decide⟩


theorem gc74b_brEnds2_badD_data :
    ({1, 2} : Finset (Fin 5)) ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5))
      ∧ sources gc74b_brEnds2 ({1, 2} : Finset (Fin 5)) = ({2, 3} : Finset (Fin 4))
      ∧ degK gc74b_brEnds2 ({1, 2} : Finset (Fin 5)) 3 = 1 := by
  refine ⟨?_, by decide, by decide⟩
  rw [show (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) from by decide]
  decide


theorem gc74b_bridge_badD_fails :
    ¬ connK gc74b_brEnds2
      ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3 := by
  rw [show (({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))
        = ({0, 3} : Finset (Fin 5)) from by decide]
  intro h
  
  have inv : ∀ w : Fin 4, connK gc74b_brEnds2 ({0, 3} : Finset (Fin 5)) 0 w → w = 0 ∨ w = 1 := by
    intro w hw
    induction hw with
    | refl => exact Or.inl rfl
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hci, hdi, hcd⟩ := hstep
      rcases ih with rfl | rfl <;> (fin_cases hi <;> revert hcd hci hdi <;> revert d <;> decide)
  rcases inv 3 h with h3 | h3 <;> exact absurd h3 (by decide)


theorem gc74b_brEnds2_goodD_data :
    ({3} : Finset (Fin 5)) ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5))
      ∧ sources gc74b_brEnds2 ({3} : Finset (Fin 5)) = ({2, 3} : Finset (Fin 4))
      ∧ degK gc74b_brEnds2 ({3} : Finset (Fin 5)) 3 = 1 := by
  refine ⟨?_, by decide, by decide⟩
  rw [show (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) from by decide]
  decide


theorem gc74b_bridge_goodD_works :
    connK gc74b_brEnds2
      ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({3} : Finset (Fin 5))) 0 3 := by
  rw [show (({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({3} : Finset (Fin 5))
        = ({0, 1, 2} : Finset (Fin 5)) from by decide]
  exact (Relation.ReflTransGen.single (b := (1 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨2, by decide, by decide, by decide, by decide⟩


theorem gc74b_bridge_twoCommodity_content :
    (¬ connK gc74b_brEnds2
        ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3)
      ∧ connK gc74b_brEnds2
          ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({3} : Finset (Fin 5))) 0 3 :=
  ⟨gc74b_bridge_badD_fails, gc74b_bridge_goodD_works⟩


theorem gc74b_brEnds2_gate_fail_34 :
    ¬ connK gc74b_brEnds2 (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) 1 3 := by
  rw [show (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) = ({0, 3, 4} : Finset (Fin 5)) from by decide]
  intro h
  have inv : ∀ w : Fin 4, connK gc74b_brEnds2 ({0, 3, 4} : Finset (Fin 5)) 1 w → (w = 0 ∨ w = 1) := by
    intro w hw
    induction hw with
    | refl => decide
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hci, hdi, hcd⟩ := hstep
      rcases ih with rfl | rfl <;> (fin_cases hi <;> revert hcd hci hdi <;> revert d <;> decide)
  rcases inv 3 h with h3 | h3 <;> exact absurd h3 (by decide)


theorem gc74b_brEnds2_gate_fail_empty :
    ¬ connK gc74b_brEnds2 (({0} : Finset (Fin 5)) ∪ (∅ : Finset (Fin 5))) 1 3 := by
  rw [Finset.union_empty]
  intro h
  have inv : ∀ w : Fin 4, connK gc74b_brEnds2 ({0} : Finset (Fin 5)) 1 w → (w = 0 ∨ w = 1) := by
    intro w hw
    induction hw with
    | refl => decide
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hci, hdi, hcd⟩ := hstep
      rcases ih with rfl | rfl <;> (fin_cases hi <;> revert hcd hci hdi <;> revert d <;> decide)
  rcases inv 3 h with h3 | h3 <;> exact absurd h3 (by decide)


theorem gc74b_brEnds2_gate_124 :
    connK gc74b_brEnds2 (({0} : Finset (Fin 5)) ∪ ({1, 2, 4} : Finset (Fin 5))) 1 3 :=
  Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩


theorem gc74b_brEnds2_LblockSet :
    gc51_LblockSet gc74b_brEnds2 ({0} : Finset (Fin 5)) 0 1 3
      = ({({1, 2, 3} : Finset (Fin 5)), ({1, 2, 4} : Finset (Fin 5))} : Finset (Finset (Fin 5))) := by
  rw [gc51_LblockSet]
  rw [show (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) from by decide]
  have hset : ({1, 2, 3, 4} : Finset (Fin 5)).powerset.filter
      (fun L => sources gc74b_brEnds2 L = (∅ : Finset (Fin 4)))
      = ({∅, {3, 4}, {1, 2, 3}, {1, 2, 4}} : Finset (Finset (Fin 5))) := by decide
  rw [show ({1, 2, 3, 4} : Finset (Fin 5)).powerset.filter
        (fun L => sources gc74b_brEnds2 L = (∅ : Finset (Fin 4))
          ∧ connK gc74b_brEnds2 (({0} : Finset (Fin 5)) ∪ L) 1 3)
      = (({1, 2, 3, 4} : Finset (Fin 5)).powerset.filter
          (fun L => sources gc74b_brEnds2 L = (∅ : Finset (Fin 4)))).filter
            (fun L => connK gc74b_brEnds2 (({0} : Finset (Fin 5)) ∪ L) 1 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  ext L
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hLmem, hconn⟩
    rcases hLmem with rfl | rfl | rfl | rfl
    · exact absurd hconn gc74b_brEnds2_gate_fail_empty
    · exact absurd hconn gc74b_brEnds2_gate_fail_34
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨by simp, gc74b_brEnds2_gate⟩
    · exact ⟨by simp, gc74b_brEnds2_gate_124⟩


theorem gc74b_brEnds2_surv_123 :
    connK gc74b_brEnds2
      ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({3} : Finset (Fin 5))) 0 3 :=
  gc74b_bridge_goodD_works


theorem gc74b_brEnds2_surv_124 :
    connK gc74b_brEnds2
      ((({0} : Finset (Fin 5)) ∪ ({1, 2, 4} : Finset (Fin 5))) \ ({3} : Finset (Fin 5))) 0 3 := by
  rw [show (({0} : Finset (Fin 5)) ∪ ({1, 2, 4} : Finset (Fin 5))) \ ({3} : Finset (Fin 5))
        = ({0, 1, 2, 4} : Finset (Fin 5)) from by decide]
  exact (Relation.ReflTransGen.single (b := (1 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨2, by decide, by decide, by decide, by decide⟩


theorem gc74b_bridge_twoCommodityLeaf :
    gc71_TwoCommodityLeaf gc74b_brEnds2 ({0} : Finset (Fin 5)) 0 1 2 3 := by
  refine gc73b_twoCommodityLeaf_of_notCut gc74b_brEnds2 gc74b_brEnds2_loopless
    ({0} : Finset (Fin 5)) (by decide) gc74b_brEnds2_goodD_data.1 gc74b_brEnds2_goodD_data.2.1
    gc74b_brEnds2_goodD_data.2.2 ?_
  intro L hL
  rw [gc74b_brEnds2_LblockSet] at hL
  simp only [Finset.mem_insert, Finset.mem_singleton] at hL
  rcases hL with rfl | rfl
  · exact gc74b_brEnds2_surv_123
  · exact gc74b_brEnds2_surv_124


theorem gc74b_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (K L D : Finset ι) (eStar : ι) (o g : W),
        (¬ connK ends ((K ∪ L) \ ({eStar} : Finset ι)) o g) →
        connK ends ((K ∪ L) \ D) o g → eStar ∉ D)
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W)
      (D : Finset ι),
        o ≠ g → D ⊆ univ \ K → sources ends D = ({y, g} : Finset W) → degK ends D g = 1 →
        (∀ L ∈ gc51_LblockSet ends K o x g,
          ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W)
            ∧ Disjoint P D ∧ connK ends P o g) →
        gc71_TwoCommodityLeaf ends K o x y g)
    ∧ 
    ((¬ connK gc74b_brEnds2
        ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3)
      ∧ connK gc74b_brEnds2
          ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({3} : Finset (Fin 5))) 0 3)
    ∧ 
    gc71_TwoCommodityLeaf gc74b_brEnds2 ({0} : Finset (Fin 5)) 0 1 2 3 :=
  ⟨fun ends K L D eStar o g hbridge hsurv =>
      gc74b_bridgeEdge_notMem_of_survives ends hbridge hsurv,
    fun ends hnd K o x y g D hog hDV hDsrc hD1 hconn =>
      gc74b_twoCommodityLeaf_of_bridgeConnectors ends hnd K hog hDV hDsrc hD1 hconn,
    gc74b_bridge_twoCommodity_content,
    gc74b_bridge_twoCommodityLeaf⟩

end StatMech.Walls
