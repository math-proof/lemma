/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc56pathremoval.Part3
import Def.StatisticalMechanics.Code.Walls.gc57menger
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

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc57_removalSurvival_of_disjointConnector (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (h : gc57_DisjointConnector ends K o x y g) :
    gc55_RemovalSurvival ends K o x y g := by
  obtain ⟨D, hDV, hDsrc, hconn⟩ := h
  refine ⟨D, hDV, hDsrc, ?_⟩
  intro L hL
  
  have hKD : Disjoint K D := by
    rw [Finset.disjoint_left]
    intro i hiK hiD
    exact (Finset.mem_sdiff.1 (hDV hiD)).2 hiK
  have hGE : (K ∪ L) \ D = K ∪ (L \ D) := gc57_graph_sdiff K L D hKD
  obtain ⟨P, hPG, hPD, hPconn⟩ := hconn L hL
  have := gc57_connK_of_disjoint_connector ends hPG hPD hPconn
  rwa [hGE] at this


theorem gc57_disjointConnector_of_removalSurvival (ends : ι → Sym2 W) (K : Finset ι) {L D : Finset ι}
    (hKD : Disjoint K D) {x g : W} (hrs : connK ends (K ∪ (L \ D)) x g) :
    ∃ P, P ⊆ K ∪ L ∧ Disjoint P D ∧ connK ends P x g := by
  refine ⟨K ∪ (L \ D), ?_, ?_, hrs⟩
  · exact Finset.union_subset_union_right (Finset.sdiff_subset)
  · rw [Finset.disjoint_union_left]
    exact ⟨hKD, Finset.disjoint_left.2 (fun i hi => (Finset.mem_sdiff.1 hi).2)⟩


theorem gc57_disjointConnector_iff_removalSurvival (ends : ι → Sym2 W) (K : Finset ι) {L D : Finset ι}
    (hKD : Disjoint K D) {x g : W} :
    (∃ P, P ⊆ K ∪ L ∧ Disjoint P D ∧ connK ends P x g) ↔ connK ends (K ∪ (L \ D)) x g := by
  constructor
  · rintro ⟨P, hPG, hPD, hPconn⟩
    have := gc57_connK_of_disjoint_connector ends hPG hPD hPconn
    rwa [gc57_graph_sdiff K L D hKD] at this
  · intro hrs
    exact gc57_disjointConnector_of_removalSurvival ends K hKD hrs


theorem gc57_disjointConnector_iff_removalSurvival_residue (ends : ι → Sym2 W) (K : Finset ι)
    {o x y g : W} :
    gc57_DisjointConnector ends K o x y g ↔ gc55_RemovalSurvival ends K o x y g := by
  constructor
  · exact gc57_removalSurvival_of_disjointConnector ends K
  · rintro ⟨D, hDV, hDsrc, hrs⟩
    have hKD : Disjoint K D := by
      rw [Finset.disjoint_left]
      intro i hiK hiD
      exact (Finset.mem_sdiff.1 (hDV hiD)).2 hiK
    refine ⟨D, hDV, hDsrc, ?_⟩
    intro L hL
    exact (gc57_disjointConnector_iff_removalSurvival ends K hKD).2 (hrs L hL)


theorem gc57_countIneq_of_disjointConnector (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc57_DisjointConnector ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc55_countIneq_of_removalSurvival ends hnd hox hoy hog hxy hxg hyg huniv
    (fun K hK => gc57_removalSurvival_of_disjointConnector ends K (h K hK))


theorem gc57_disjointConnector_of_disjoint (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hdisj : ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) :
    gc57_DisjointConnector ends K o x y g := by
  refine ⟨D, hDV, hDsrc, ?_⟩
  intro L hL
  have hLmem := hL
  rw [gc51_LblockSet, Finset.mem_filter, Finset.mem_powerset] at hL
  obtain ⟨_, _, hgate⟩ := hL
  have hKD : Disjoint K D := by
    rw [Finset.disjoint_left]
    intro i hiK hiD
    exact (Finset.mem_sdiff.1 (hDV hiD)).2 hiK
  refine ⟨K ∪ L, Finset.Subset.refl _, ?_, hgate⟩
  rw [Finset.disjoint_union_left]
  exact ⟨hKD, hdisj L hLmem⟩


theorem gc57_disjointConnector_of_ygEdge (ends : ι → Sym2 W) (hnd : ∀ j : ι, ¬ (ends j).IsDiag)
    (K : Finset ι) {o x y g : W} (hyg : y ≠ g) {i : ι} (hiV : i ∈ univ \ K) (hi : ends i = s(y, g)) :
    gc57_DisjointConnector ends K o x y g :=
  (gc57_disjointConnector_iff_removalSurvival_residue ends K).2
    (gc55_removalSurvival_of_ygEdge ends hnd K hyg hiV hi)

end Abstract

open Classical


theorem gc57_witness_disjointConnector_K13 :
    gc57_DisjointConnector gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 := by
  apply gc57_disjointConnector_of_disjoint (D := ({0, 2} : Finset (Fin 4)))
  · rw [show (univ : Finset (Fin 4)) \ ({1, 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) from by decide]
  · decide
  · intro L hL
    rw [gc51_witness_LblockSet_K13, Finset.mem_singleton] at hL
    subst hL
    exact Finset.disjoint_empty_left _


theorem gc57_witness_disjointConnector_K23 :
    gc57_DisjointConnector gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 := by
  apply gc57_disjointConnector_of_disjoint (D := ({0, 1} : Finset (Fin 4)))
  · rw [show (univ : Finset (Fin 4)) \ ({2, 3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) from by decide]
  · decide
  · intro L hL
    rw [gc51_witness_LblockSet_K23, Finset.mem_singleton] at hL
    subst hL
    exact Finset.disjoint_empty_left _


theorem gc57_witness_cosetGateDom : gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
  apply gc55_cosetGateDom_of_removalSurvival
  intro K hK
  rw [gc50_witness_oxCurrents] at hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hK
  rcases hK with rfl | rfl
  · exact gc57_removalSurvival_of_disjointConnector gc49_witnessEnds _ gc57_witness_disjointConnector_K13
  · exact gc57_removalSurvival_of_disjointConnector gc49_witnessEnds _ gc57_witness_disjointConnector_K23


theorem gc57_witness_perKCount : gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 :=
  gc53_perKCount_of_cosetGateDom gc49_witnessEnds gc49_witnessEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc49_witnessEnds_univ_sources gc57_witness_cosetGateDom


end StatMech.Walls
