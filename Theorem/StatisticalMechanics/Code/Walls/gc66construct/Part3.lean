/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc65cyclespace.Part2
import Def.StatisticalMechanics.Code.Walls.gc66construct.Part2
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

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc66_gDeg1Connector_of_removalSurvival (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hxg : x ≠ g)
    (h : gc66_GDeg1RemovalSurvival ends K o x y g) :
    gc65_GDeg1Connector ends K o x y g := by
  obtain ⟨D, hDV, hDsrc, hD1, hsurv⟩ := h
  refine ⟨D, hDV, hDsrc, hD1, ?_⟩
  intro L hL
  
  have hbase : connK ends ((K ∪ L) \ D) x g := hsurv L hL
  have hPD : Disjoint ((K ∪ L) \ D) D := by
    rw [Finset.disjoint_left]; intro i hi; exact (Finset.mem_sdiff.1 hi).2
  exact gc65_trim_to_boundary ends hnd hxg (Finset.sdiff_subset) hPD hbase


theorem gc66_sharedSinkFixedD_of_removalSurvival (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (h : gc66_GDeg1RemovalSurvival ends K o x y g) :
    gc64_SharedSinkFixedD ends K o x y g := by
  obtain ⟨D, hDV, hDsrc, _, hsurv⟩ := h
  exact ⟨D, hDV, hDsrc, hsurv⟩


theorem gc66_disjointConnector_of_removalSurvival (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hxg : x ≠ g)
    (h : gc66_GDeg1RemovalSurvival ends K o x y g) :
    gc57_DisjointConnector ends K o x y g :=
  gc65_disjointConnector_of_gDeg1Connector ends K
    (gc66_gDeg1Connector_of_removalSurvival ends hnd K hxg h)


theorem gc66_countIneq_of_removalSurvival (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc66_GDeg1RemovalSurvival ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc57_countIneq_of_disjointConnector ends hnd hox hoy hog hxy hxg hyg huniv
    (fun K hK => gc66_disjointConnector_of_removalSurvival ends hnd K hxg (h K hK))


theorem gc66_removalSurvival_of_disjoint (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hD1 : degK ends D g = 1) (hdisj : ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) :
    gc66_GDeg1RemovalSurvival ends K o x y g := by
  refine ⟨D, hDV, hDsrc, hD1, ?_⟩
  intro L hL
  have hLmem := hL
  rw [gc51_LblockSet, Finset.mem_filter, Finset.mem_powerset] at hL
  obtain ⟨_, _, hgate⟩ := hL
  have hKD : Disjoint K D := by
    rw [Finset.disjoint_left]; intro i hiK hiD
    exact (Finset.mem_sdiff.1 (hDV hiD)).2 hiK
  have heq : (K ∪ L) \ D = K ∪ L := by
    rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_union_left]
    exact ⟨hKD, hdisj L hLmem⟩
  rw [heq]; exact hgate


theorem gc66_removalSurvival_of_gDeg1Witness (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hD1 : degK ends D g = 1)
    (hsurv : ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) x g) :
    gc66_GDeg1RemovalSurvival ends K o x y g :=
  ⟨D, hDV, hDsrc, hD1, hsurv⟩

end Abstract

open Classical


theorem gc66_witness_surv_23 :
    connK gc59_witnessEnds ((({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 1 3 := by
  rw [show (({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))
        = ({0, 3} : Finset (Fin 5)) from by decide]
  exact gc65_witness_P23_conn


theorem gc66_witness_surv_24 :
    connK gc59_witnessEnds ((({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 1 3 := by
  rw [show (({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))
        = ({0, 4} : Finset (Fin 5)) from by decide]
  exact gc65_witness_P24_conn


theorem gc66_witness_surv_34 :
    connK gc59_witnessEnds ((({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 1 3 := by
  rw [show (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))
        = ({0, 3, 4} : Finset (Fin 5)) from by decide]
  exact (Relation.ReflTransGen.single (b := (0 : Fin 4)) ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨3, by decide, by decide, by decide, by decide⟩


theorem gc66_witness_choose_D :
    ∃ D, D ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5))
      ∧ sources gc59_witnessEnds D = ({2, 3} : Finset (Fin 4)) ∧ degK gc59_witnessEnds D 3 = 1 := by
  refine ⟨({1, 2} : Finset (Fin 5)), ?_, gc59_witnessEnds_D_sources, gc65_witness_D_gDeg1⟩
  rw [show (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) from by decide]
  decide


theorem gc66_witness_removalSurvival :
    gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
  refine gc66_removalSurvival_of_gDeg1Witness gc59_witnessEnds _ ?_ gc59_witnessEnds_D_sources
    gc65_witness_D_gDeg1 ?_
  · rw [show (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) from by decide]
    decide
  · intro L hL
    rw [gc59_witness_LblockSet] at hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl
    · exact gc66_witness_surv_23
    · exact gc66_witness_surv_24
    · exact gc66_witness_surv_34


theorem gc66_witness_removableGEdge :
    gc66_RemovableGEdge gc59_witnessEnds ({0} : Finset (Fin 5)) 2 3 := by
  intro D hDV hDsrc hdeg2
  
  have hVeq : (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) := by
    decide
  rw [hVeq] at hDV
  have hDeq : D = ({1, 2, 3, 4} : Finset (Fin 5)) := by
    have hmem : D ∈ (({1, 2, 3, 4} : Finset (Fin 5)).powerset.filter
        (fun D => sources gc59_witnessEnds D = ({2, 3} : Finset (Fin 4)) ∧ 2 ≤ degK gc59_witnessEnds D 3)) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hDV, hDsrc, hdeg2⟩
    have hset : (({1, 2, 3, 4} : Finset (Fin 5)).powerset.filter
        (fun D => sources gc59_witnessEnds D = ({2, 3} : Finset (Fin 4)) ∧ 2 ≤ degK gc59_witnessEnds D 3))
        = ({({1, 2, 3, 4} : Finset (Fin 5))} : Finset (Finset (Fin 5))) := by decide
    rw [hset, Finset.mem_singleton] at hmem
    exact hmem
  subst hDeq
  refine ⟨2, by decide, by decide, ?_⟩
  rw [show ({1, 2, 3, 4} : Finset (Fin 5)) \ ({2} : Finset (Fin 5)) = ({1, 3, 4} : Finset (Fin 5)) from by decide]
  exact (Relation.ReflTransGen.single (b := (0 : Fin 4)) ⟨1, by decide, by decide, by decide, by decide⟩).tail
    ⟨3, by decide, by decide, by decide, by decide⟩


theorem gc66_witness_choose_D_via_hyp :
    ∃ D, D ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5))
      ∧ sources gc59_witnessEnds D = ({2, 3} : Finset (Fin 4)) ∧ degK gc59_witnessEnds D 3 = 1 :=
  gc66_choose_D gc59_witnessEnds gc59_witnessEnds_loopless ({0} : Finset (Fin 5))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    gc59_witnessEnds_univ_sources gc59_witnessEnds_K_sources gc66_witness_removableGEdge


theorem gc66_witness_gDeg1Connector :
    gc65_GDeg1Connector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  gc66_gDeg1Connector_of_removalSurvival gc59_witnessEnds gc59_witnessEnds_loopless _
    (by decide) gc66_witness_removalSurvival


theorem gc66_witness_disjointConnector :
    gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  gc66_disjointConnector_of_removalSurvival gc59_witnessEnds gc59_witnessEnds_loopless _
    (by decide) gc66_witness_removalSurvival


theorem gc66_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W),
        x ≠ g → gc66_GDeg1RemovalSurvival ends K o x y g → gc65_GDeg1Connector ends K o x y g)
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W),
        x ≠ g → gc66_GDeg1RemovalSurvival ends K o x y g → gc57_DisjointConnector ends K o x y g)
    ∧ 
    (∃ D, D ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5))
      ∧ sources gc59_witnessEnds D = ({2, 3} : Finset (Fin 4)) ∧ degK gc59_witnessEnds D 3 = 1)
    ∧ 
    gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3
    ∧ 
    gc65_GDeg1Connector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3
    ∧ gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  ⟨fun ends hnd K o x y g hxg h => gc66_gDeg1Connector_of_removalSurvival ends hnd K hxg h,
    fun ends hnd K o x y g hxg h => gc66_disjointConnector_of_removalSurvival ends hnd K hxg h,
    gc66_witness_choose_D,
    gc66_witness_removalSurvival,
    gc66_witness_gDeg1Connector,
    gc66_witness_disjointConnector⟩

end StatMech.Walls
