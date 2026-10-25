/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc42countproof.Part2
import Def.StatisticalMechanics.Code.Walls.gc43graham.Part2
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


theorem gc43_EMass_of_fibreDomReloc (ends : ι → Sym2 W) (o x y g : W)
    (h : gc43_FibreDomReloc ends o x y g) :
    gc42_EMassResidue ends o x y g := by
  obtain ⟨φ, hmaps, hfib⟩ := h
  unfold gc42_EMassResidue
  rw [gc43_LHS_eq_gatedSum, gc43_RHS_eq_gatedSum]
  
  have hpart : ∑ M ∈ gc43_Lset ends o x y g, gc40_E ends M
      = ∑ M' ∈ gc43_Rset ends o x y g,
          ∑ M ∈ (gc43_Lset ends o x y g).filter (fun M => φ M = M'), gc40_E ends M :=
    (Finset.sum_fiberwise_of_maps_to (fun M hM => hmaps M hM) (fun M => gc40_E ends M)).symm
  rw [hpart]
  exact Finset.sum_le_sum (fun M' hM' => hfib M' hM')


theorem gc43_countIneq_of_fibreDomReloc (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : gc43_FibreDomReloc ends o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc42_countIneq_of_EMass ends hnd hox hoy hog hxy hxg hyg huniv
    (gc43_EMass_of_fibreDomReloc ends o x y g h)


theorem gc43_per_M_reloc_exists (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    {M : Finset ι} (hM : M ∈ gc43_Lset ends o x y g) :
    ∃ M' ∈ gc43_Rset ends o x y g, M ⊆ M' ∧ gc40_E ends M ≤ gc40_E ends M' := by
  rw [gc43_Lset, Finset.mem_filter, Finset.mem_powerset] at hM
  obtain ⟨hMuniv, hMsrc, hMgate⟩ := hM
  obtain ⟨Q, hQsub, hQsrc⟩ :=
    gc43_exists_reloc_set ends hnd M hox hoy hog hxy hxg hyg huniv hMsrc
  refine ⟨M ∪ Q, ?_, Finset.subset_union_left, gc43_reloc_E_dom ends M Q⟩
  rw [gc43_Rset, Finset.mem_filter, Finset.mem_powerset]
  obtain ⟨hsrc', hox', hoy', hog'⟩ :=
    gc43_reloc_in_RHS ends hnd hQsub hox hoy hog hxy hxg hyg hMsrc hQsrc hMgate
  exact ⟨Finset.subset_univ _, hsrc', hox', hoy', hog'⟩

end Abstract


theorem gc43_claw_Lset :
    gc43_Lset gc40_clawEnds (0 : Fin 4) 1 2 3 = {({0, 1} : Finset (Fin 3))} := by
  rw [gc43_Lset]
  
  rw [← Finset.filter_filter]
  rw [show ((univ : Finset (Fin 3)).powerset.filter
        (fun M => sources gc40_clawEnds M = ({0, 1} : Finset (Fin 4))))
      = {({0, 1} : Finset (Fin 3))} from by decide]
  
  have hL : connK gc40_clawEnds ({0, 1} : Finset (Fin 3)) (1 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩
  rw [Finset.filter_singleton, if_pos hL]


theorem gc43_claw_Rset :
    gc43_Rset gc40_clawEnds (0 : Fin 4) 1 2 3 = {({0, 1, 2} : Finset (Fin 3))} := by
  rw [gc43_Rset]
  rw [← Finset.filter_filter]
  rw [show ((univ : Finset (Fin 3)).powerset.filter
        (fun M => sources gc40_clawEnds M = ({0, 1, 2, 3} : Finset (Fin 4))))
      = {({0, 1, 2} : Finset (Fin 3))} from by decide]
  have h01 : connK gc40_clawEnds ({0, 1, 2} : Finset (Fin 3)) (0 : Fin 4) (1 : Fin 4) :=
    Relation.ReflTransGen.head (b := (3 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩)
  have h02 : connK gc40_clawEnds ({0, 1, 2} : Finset (Fin 3)) (0 : Fin 4) (2 : Fin 4) :=
    Relation.ReflTransGen.head (b := (3 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩)
  have h03 : connK gc40_clawEnds ({0, 1, 2} : Finset (Fin 3)) (0 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩
  rw [Finset.filter_singleton, if_pos ⟨h01, h02, h03⟩]


theorem gc43_claw_FibreDomReloc : gc43_FibreDomReloc gc40_clawEnds (0 : Fin 4) 1 2 3 := by
  refine ⟨fun _ => ({0, 1, 2} : Finset (Fin 3)), ?_, ?_⟩
  · intro M hM
    rw [gc43_claw_Rset, Finset.mem_singleton]
  · intro M' hM'
    rw [gc43_claw_Rset, Finset.mem_singleton] at hM'
    subst hM'
    rw [gc43_claw_Lset]
    
    rw [show ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))).filter
          (fun M => ({0, 1, 2} : Finset (Fin 3)) = ({0, 1, 2} : Finset (Fin 3)))
        = {({0, 1} : Finset (Fin 3))} from by decide]
    rw [Finset.sum_singleton]
    rw [show gc40_E gc40_clawEnds ({0, 1} : Finset (Fin 3)) = 1 from by decide,
      show gc40_E gc40_clawEnds ({0, 1, 2} : Finset (Fin 3)) = 1 from by decide]


theorem gc43_claw_core : gc39_ThreeColouringCountIneq gc40_clawEnds (0 : Fin 4) 1 2 3 :=
  gc43_countIneq_of_fibreDomReloc gc40_clawEnds gc40_clawEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc40_clawEnds_univ_sources gc43_claw_FibreDomReloc


theorem gc43_reloc_applies_claw :
    (∀ i : Fin 3, ¬ (gc40_clawEnds i).IsDiag)
      ∧ ((0 : Fin 4) ≠ 1 ∧ (0 : Fin 4) ≠ 2 ∧ (0 : Fin 4) ≠ 3
          ∧ (1 : Fin 4) ≠ 2 ∧ (1 : Fin 4) ≠ 3 ∧ (2 : Fin 4) ≠ 3)
      ∧ sources gc40_clawEnds (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4))
      ∧ gc43_FibreDomReloc gc40_clawEnds (0 : Fin 4) 1 2 3 :=
  ⟨gc40_clawEnds_loopless, ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩,
    gc40_clawEnds_univ_sources, gc43_claw_FibreDomReloc⟩

end StatMech.Walls
