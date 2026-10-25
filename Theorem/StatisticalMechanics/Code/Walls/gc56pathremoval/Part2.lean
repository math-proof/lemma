/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc55graham.Part2
import Def.StatisticalMechanics.Code.Walls.gc56pathremoval
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


theorem gc56_removalSurvival_of_pathReconnect (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (h : gc56_PathReconnect ends K o x y g) :
    gc55_RemovalSurvival ends K o x y g := by
  obtain ⟨D, hDV, hDsrc, hrec⟩ := h
  refine ⟨D, hDV, hDsrc, ?_⟩
  intro L hL
  have hLmem := hL
  rw [gc51_LblockSet, Finset.mem_filter, Finset.mem_powerset] at hL
  obtain ⟨hLV, hLsrc, hgate⟩ := hL
  
  have hKD : Disjoint K D := by
    rw [Finset.disjoint_left]
    intro i hiK hiD
    have := hDV hiD
    rw [Finset.mem_sdiff] at this
    exact this.2 hiK
  
  have hGE : (K ∪ L) \ (L ∩ D) = K ∪ (L \ D) := gc56_graph_restrict K L D hKD
  
  have hrec' : ∀ i ∈ L ∩ D, ∀ p q : W, ends i = s(p, q) →
      connK ends ((K ∪ L) \ (L ∩ D)) p q := by
    intro i hi p q hpq
    rw [hGE]
    exact hrec L hLmem i hi p q hpq
  have := gc56_multiRemove ends (K ∪ L) (L ∩ D) hrec' hgate
  rwa [hGE] at this


theorem gc56_pathReconnect_of_disjoint (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hdisj : ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) :
    gc56_PathReconnect ends K o x y g := by
  refine ⟨D, hDV, hDsrc, ?_⟩
  intro L hL i hi p q hpq
  rw [Finset.mem_inter] at hi
  exact absurd hi.2 (Finset.disjoint_left.1 (hdisj L hL) hi.1)


theorem gc56_pathReconnect_of_ygEdge (ends : ι → Sym2 W) (hnd : ∀ j : ι, ¬ (ends j).IsDiag)
    (K : Finset ι) {o x y g : W} (hyg : y ≠ g) {i : ι} (hiV : i ∈ univ \ K) (hi : ends i = s(y, g)) :
    gc56_PathReconnect ends K o x y g := by
  refine ⟨{i}, by simpa using hiV, gc55_sources_singleton ends i hyg hi, ?_⟩
  intro L hL j hj p q hpq
  
  rw [Finset.mem_inter, Finset.mem_singleton] at hj
  obtain ⟨hjL, hji⟩ := hj
  subst hji
  
  have hLsrc : sources ends L = (∅ : Finset W) := by
    rw [gc51_LblockSet, Finset.mem_filter, Finset.mem_powerset] at hL
    exact hL.2.1
  
  have hygL : connK ends (L \ {j}) y g :=
    gc55_yg_conn_of_removed_edge ends hnd L j hyg hjL hLsrc hi
  have hygKL : connK ends (K ∪ (L \ {j})) y g :=
    gc51_connK_mono ends Finset.subset_union_right hygL
  
  have heq : s(p, q) = s(y, g) := by rw [← hpq, hi]
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hygKL
  · exact connK_symm ends _ hygKL


theorem gc56_countIneq_of_pathReconnect (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc56_PathReconnect ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc55_countIneq_of_removalSurvival ends hnd hox hoy hog hxy hxg hyg huniv
    (fun K hK => gc56_removalSurvival_of_pathReconnect ends K (h K hK))

end Abstract

open Classical


theorem gc56_witness_pathReconnect_K13 :
    gc56_PathReconnect gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 := by
  apply gc56_pathReconnect_of_disjoint (D := ({0, 2} : Finset (Fin 4)))
  · rw [show (univ : Finset (Fin 4)) \ ({1, 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) from by decide]
  · decide
  · intro L hL
    rw [gc51_witness_LblockSet_K13, Finset.mem_singleton] at hL
    subst hL
    exact Finset.disjoint_empty_left _


theorem gc56_witness_pathReconnect_K23 :
    gc56_PathReconnect gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 := by
  apply gc56_pathReconnect_of_disjoint (D := ({0, 1} : Finset (Fin 4)))
  · rw [show (univ : Finset (Fin 4)) \ ({2, 3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) from by decide]
  · decide
  · intro L hL
    rw [gc51_witness_LblockSet_K23, Finset.mem_singleton] at hL
    subst hL
    exact Finset.disjoint_empty_left _


theorem gc56_witness_cosetGateDom : gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
  apply gc55_cosetGateDom_of_removalSurvival
  intro K hK
  rw [gc50_witness_oxCurrents] at hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hK
  rcases hK with rfl | rfl
  · exact gc56_removalSurvival_of_pathReconnect gc49_witnessEnds _ gc56_witness_pathReconnect_K13
  · exact gc56_removalSurvival_of_pathReconnect gc49_witnessEnds _ gc56_witness_pathReconnect_K23


theorem gc56_witness_perKCount : gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 :=
  gc53_perKCount_of_cosetGateDom gc49_witnessEnds gc49_witnessEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc49_witnessEnds_univ_sources gc56_witness_cosetGateDom


end StatMech.Walls
