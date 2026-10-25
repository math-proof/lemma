/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc68removalsurvival.Part2
import Theorem.StatisticalMechanics.Code.Walls.menger_general.Part7
import Theorem.StatisticalMechanics.Code.Walls.gc63reroute.Part2
import Def.StatisticalMechanics.Code.Walls.gc69mengerclose.Part2
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


theorem gc69b_minConnector_gDeg1 (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {y g : W} (hyg : y ≠ g) {D : Finset ι} (hDV : D ⊆ univ \ K)
    (hDsrc : sources ends D = ({y, g} : Finset W))
    (hDmin : ∀ D', D' ⊆ univ \ K → sources ends D' = ({y, g} : Finset W) → #D ≤ #D') :
    degK ends D g = 1 := by
  have hodd : Odd (degK ends D g) := gc65_ygConnector_gDeg_odd ends hDsrc
  have hge1 : 1 ≤ degK ends D g := hodd.pos
  by_contra hne
  have hge2 : 2 ≤ degK ends D g := by omega
  obtain ⟨i₀, hi₀D, hi₀g, hi₀conn⟩ := gc67b_removableGEdge ends hnd K hyg D hDV hDsrc hge2
  obtain ⟨D', hD'D, hD'src, hlt⟩ := gc66_strictly_smaller_of_removable ends hyg hi₀D hi₀conn
  have hD'V : D' ⊆ univ \ K := hD'D.trans hDV
  exact absurd (hDmin D' hD'V hD'src) (by omega)


theorem gc69b_removalSurvival_of_ogSurvival (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hyg : y ≠ g)
    (h : gc69b_OGSurvival ends K o x y g) :
    gc66_GDeg1RemovalSurvival ends K o x y g := by
  obtain ⟨D, hDV, hDsrc, hDmin, hsurv⟩ := h
  exact ⟨D, hDV, hDsrc, gc69b_minConnector_gDeg1 ends hnd K hyg hDV hDsrc hDmin, hsurv⟩


theorem gc69b_countIneq_of_ogSurvival (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc69b_OGSurvival ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g := by
  apply gc66_countIneq_of_removalSurvival ends hnd hox hoy hog hxy hxg hyg huniv
  intro K hK
  exact gc69b_removalSurvival_of_ogSurvival ends hnd K hyg (h K hK)


theorem gc69b_relConn2_false_of_bridge (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G C : Finset ι} {o g : W} (hog : o ≠ g)
    (hC : mngg_IsCut ends G o g C) (hC1 : #C = 1) :
    ¬ mngg_RelConn ends G o g 2 := by
  intro hrel
  obtain ⟨⟨P, hP⟩, hcut⟩ := mngg_maxflow_mincut ends hnd hog 2 hrel
  have : (2 : ℕ) ≤ #C := hcut C hC
  omega

end Abstract

open Classical


theorem gc69b_witness_disjointOGConnector :
    gc69b_DisjointOGConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  gc69b_disjointOGConnector_of_ogReroute gc59_witnessEnds gc59_witnessEnds_loopless
    ({0} : Finset (Fin 5)) (by decide) gc68_witness_ogReroute


theorem gc69b_witness_removalSurvival :
    gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  gc69b_removalSurvival_of_disjointOGConnector gc59_witnessEnds gc59_witnessEnds_loopless _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc59_witnessEnds_univ_sources gc59_witnessEnds_K_sources gc69b_witness_disjointOGConnector


theorem gc69b_witness_ogSurvival :
    gc69b_OGSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
  obtain ⟨D, hDV, hDsrc, hD1, hsurv⟩ := gc66_witness_removalSurvival
  
  refine ⟨({1, 2} : Finset (Fin 5)), ?_, gc59_witnessEnds_D_sources, ?_, ?_⟩
  · rw [show (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) from by decide]
    decide
  · 
    intro D' hD'V hD'src
    have hVeq : (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) := by decide
    rw [hVeq] at hD'V
    have hlb : ∀ D'' ∈ ({1, 2, 3, 4} : Finset (Fin 5)).powerset,
        sources gc59_witnessEnds D'' = ({2, 3} : Finset (Fin 4)) → 2 ≤ #D'' := by decide
    have := hlb D' (Finset.mem_powerset.2 hD'V) hD'src
    simpa using this
  · 
    intro L hL
    rw [gc59_witness_LblockSet] at hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl
    · exact gc66_witness_surv_23
    · exact gc66_witness_surv_24
    · exact gc66_witness_surv_34


theorem gc69b_witness_removalSurvival_via_ogSurvival :
    gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  gc69b_removalSurvival_of_ogSurvival gc59_witnessEnds gc59_witnessEnds_loopless _
    (by decide) gc69b_witness_ogSurvival


end StatMech.Walls
