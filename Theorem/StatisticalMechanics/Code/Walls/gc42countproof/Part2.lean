/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc42countproof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc40count.Part5
import Def.StatisticalMechanics.Code.Walls.gc42countproof
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  exists_conn_set sources_symmDiff path_exists mem_sources)


section Abstract

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc42_countIneq_of_EMass (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hres : gc42_EMassResidue ends o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g := by
  rw [gc40_countIneq_iff, gc42_NR_eq_Mform ends hnd hox hoy hog hxy hxg hyg huniv,
    gc42_NL_eq_Mform ends huniv]
  exact hres


theorem gc42_NRterm_le_E (ends : ι → Sym2 W) (M : Finset ι) {x g : W} :
    (if connK ends M x g then gc40_E ends M else 0) ≤ gc40_E ends M := by
  by_cases h : connK ends M x g
  · rw [if_pos h]
  · rw [if_neg h]; exact Nat.zero_le _


theorem gc42_NLterm_le_E (ends : ι → Sym2 W) (M : Finset ι) {o x y g : W} :
    (if connK ends M o x ∧ connK ends M o y ∧ connK ends M o g then gc40_E ends M else 0)
      ≤ gc40_E ends M := by
  by_cases h : connK ends M o x ∧ connK ends M o y ∧ connK ends M o g
  · rw [if_pos h]
  · rw [if_neg h]; exact Nat.zero_le _


theorem gc42_EMass_iff_countIneq (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W)) :
    gc42_EMassResidue ends o x y g ↔ gc39_ThreeColouringCountIneq ends o x y g := by
  constructor
  · exact gc42_countIneq_of_EMass ends hnd hox hoy hog hxy hxg hyg huniv
  · intro hcore
    rw [gc40_countIneq_iff, gc42_NR_eq_Mform ends hnd hox hoy hog hxy hxg hyg huniv,
      gc42_NL_eq_Mform ends huniv] at hcore
    exact hcore

end Abstract


theorem gc42_reduction_applies_claw :
    (∀ i : Fin 3, ¬ (gc40_clawEnds i).IsDiag)
      ∧ ((0 : Fin 4) ≠ 1 ∧ (0 : Fin 4) ≠ 2 ∧ (0 : Fin 4) ≠ 3
          ∧ (1 : Fin 4) ≠ 2 ∧ (1 : Fin 4) ≠ 3 ∧ (2 : Fin 4) ≠ 3)
      ∧ sources gc40_clawEnds (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4)) :=
  ⟨gc40_clawEnds_loopless, ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩,
    gc40_clawEnds_univ_sources⟩


theorem gc42_claw_residue_closes_core
    (hres : gc42_EMassResidue gc40_clawEnds (0 : Fin 4) 1 2 3) :
    gc39_ThreeColouringCountIneq gc40_clawEnds (0 : Fin 4) 1 2 3 :=
  gc42_countIneq_of_EMass gc40_clawEnds gc40_clawEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc40_clawEnds_univ_sources hres


theorem gc42_claw_EMassResidue : gc42_EMassResidue gc40_clawEnds (0 : Fin 4) 1 2 3 := by
  unfold gc42_EMassResidue
  
  rw [show ((univ : Finset (Fin 3)).powerset.filter
        (fun S => sources gc40_clawEnds S = ({0, 1} : Finset (Fin 4))))
      = {({0, 1} : Finset (Fin 3))} from by decide]
  rw [show ((univ : Finset (Fin 3)).powerset.filter
        (fun S => sources gc40_clawEnds S = ({0, 1, 2, 3} : Finset (Fin 4))))
      = {({0, 1, 2} : Finset (Fin 3))} from by decide]
  rw [Finset.sum_singleton, Finset.sum_singleton]
  
  have hL : connK gc40_clawEnds ({0, 1} : Finset (Fin 3)) (1 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩
  
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
  rw [if_pos hL, if_pos ⟨h01, h02, h03⟩]
  
  rw [show gc40_E gc40_clawEnds ({0, 1} : Finset (Fin 3)) = 1 from by decide,
    show gc40_E gc40_clawEnds ({0, 1, 2} : Finset (Fin 3)) = 1 from by decide]


theorem gc42_claw_core : gc39_ThreeColouringCountIneq gc40_clawEnds (0 : Fin 4) 1 2 3 :=
  gc42_claw_residue_closes_core gc42_claw_EMassResidue

end StatMech.Walls
