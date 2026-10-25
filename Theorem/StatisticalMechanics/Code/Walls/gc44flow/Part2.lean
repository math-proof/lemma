/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc44flow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc43graham.Part3
import Def.StatisticalMechanics.Code.Walls.gc44flow.Part2
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

section Abstract

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc44_FibreDomReloc_of_forest (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hforest : gc44_ForestHyp ends) (hbridge : gc44_DisjointBridge ends o x y g) :
    gc43_FibreDomReloc ends o x y g := by
  obtain ⟨P, hPsrc, hPdisj⟩ := hbridge
  refine gc44_fibreDomReloc_of_injOn_of_E_one ends o x y g hforest (fun M => M ∆ P) ?_ ?_
  · 
    intro M hM
    have hMmem := hM
    rw [gc43_Lset, Finset.mem_filter, Finset.mem_powerset] at hMmem
    obtain ⟨_, hMsrc, hMgate⟩ := hMmem
    exact gc44_shift_in_Rset_of_disjoint ends hnd (hPdisj M hM) hox hoy hog hxy hxg hyg
      hMsrc hPsrc hMgate
  · 
    exact gc44_shift_injOn ends P (gc43_Lset ends o x y g)


theorem gc44_countIneq_of_forest (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hforest : gc44_ForestHyp ends) (hbridge : gc44_DisjointBridge ends o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc43_countIneq_of_fibreDomReloc ends hnd hox hoy hog hxy hxg hyg huniv
    (gc44_FibreDomReloc_of_forest ends hnd hox hoy hog hxy hxg hyg hforest hbridge)


theorem gc44_EMassResidue_of_forest (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hforest : gc44_ForestHyp ends) (hbridge : gc44_DisjointBridge ends o x y g) :
    gc42_EMassResidue ends o x y g :=
  gc43_EMass_of_fibreDomReloc ends o x y g
    (gc44_FibreDomReloc_of_forest ends hnd hox hoy hog hxy hxg hyg hforest hbridge)

end Abstract


theorem gc44_claw_forest : gc44_ForestHyp gc40_clawEnds := by
  intro M
  revert M
  decide


theorem gc44_claw_bridge : gc44_DisjointBridge gc40_clawEnds (0 : Fin 4) 1 2 3 := by
  refine ⟨({2} : Finset (Fin 3)), by decide, ?_⟩
  intro M hM
  rw [gc43_claw_Lset, Finset.mem_singleton] at hM
  subst hM
  decide


theorem gc44_claw_FibreDomReloc : gc43_FibreDomReloc gc40_clawEnds (0 : Fin 4) 1 2 3 :=
  gc44_FibreDomReloc_of_forest gc40_clawEnds gc40_clawEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc44_claw_forest gc44_claw_bridge


theorem gc44_claw_core : gc39_ThreeColouringCountIneq gc40_clawEnds (0 : Fin 4) 1 2 3 :=
  gc44_countIneq_of_forest gc40_clawEnds gc40_clawEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc40_clawEnds_univ_sources gc44_claw_forest gc44_claw_bridge


theorem gc44_reloc_applies_claw :
    (∀ i : Fin 3, ¬ (gc40_clawEnds i).IsDiag)
      ∧ ((0 : Fin 4) ≠ 1 ∧ (0 : Fin 4) ≠ 2 ∧ (0 : Fin 4) ≠ 3
          ∧ (1 : Fin 4) ≠ 2 ∧ (1 : Fin 4) ≠ 3 ∧ (2 : Fin 4) ≠ 3)
      ∧ sources gc40_clawEnds (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4))
      ∧ gc44_ForestHyp gc40_clawEnds
      ∧ gc44_DisjointBridge gc40_clawEnds (0 : Fin 4) 1 2 3 :=
  ⟨gc40_clawEnds_loopless, ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩,
    gc40_clawEnds_univ_sources, gc44_claw_forest, gc44_claw_bridge⟩

end StatMech.Walls
