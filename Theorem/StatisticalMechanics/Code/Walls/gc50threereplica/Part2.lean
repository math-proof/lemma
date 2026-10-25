/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc49nullity2.Part3
import Def.StatisticalMechanics.Code.Walls.gc50threereplica
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

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  switching_card₂ connK_symm exists_conn_set sources_symmDiff path_exists mem_sources)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc50_LHS_eq_perKsum (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {o x g : W}
    (hox : o ≠ x) :
    (∑ m ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x} : Finset W)),
        (if connK ends m x g then gc40_E ends m else 0))
      = ∑ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
          gc50_Lblock ends K o x g := by
  
  have hstep1 :
      (∑ m ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x} : Finset W)),
          (if connK ends m x g then gc40_E ends m else 0))
        = #(((univ : Finset ι).powerset.filter
              (fun m => sources ends m = ({o, x} : Finset W) ∧ connK ends m x g)).sigma
            (fun m => m.powerset.filter (fun K => sources ends K = ({o, x} : Finset W)))) := by
    rw [Finset.card_sigma]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext m; simp only [Finset.mem_filter, Finset.mem_powerset]; tauto
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_powerset] at hm
      rw [gc50_E_eq_oxCount_of_ox_conn ends m (fun i _ => hnd i) hox hm.2.1]
  rw [hstep1]
  
  rw [gc50_reindex_by_oxCurrent ends o x ({o, x} : Finset W) (∅ : Finset W) gc50_sd_ox_ox
    (G := fun m => connK ends m x g)]
  apply Finset.sum_congr rfl
  intro K hK
  rfl


theorem gc50_sd_oxyg_ox {o x y g : W} (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) :
    ({o, x, y, g} : Finset W) ∆ ({o, x} : Finset W) = ({y, g} : Finset W) := by
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨h, hn⟩ | ⟨h, hn⟩) <;> tauto
  · rintro (rfl | rfl)
    · exact Or.inl ⟨Or.inr (Or.inr (Or.inl rfl)), not_or.2 ⟨fun h => hoy h.symm, fun h => hxy h.symm⟩⟩
    · exact Or.inl ⟨Or.inr (Or.inr (Or.inr rfl)), not_or.2 ⟨fun h => hog h.symm, fun h => hxg h.symm⟩⟩


theorem gc50_RHS_eq_perKsum (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) :
    (∑ m ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x, y, g} : Finset W)),
        (if connK ends m o x ∧ connK ends m o y ∧ connK ends m o g then gc40_E ends m else 0))
      = ∑ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
          gc50_Rblock ends K o x y g := by
  
  have hstep1 :
      (∑ m ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x, y, g} : Finset W)),
          (if connK ends m o x ∧ connK ends m o y ∧ connK ends m o g then gc40_E ends m else 0))
        = #(((univ : Finset ι).powerset.filter
              (fun m => sources ends m = ({o, x, y, g} : Finset W)
                ∧ (connK ends m o x ∧ connK ends m o y ∧ connK ends m o g))).sigma
            (fun m => m.powerset.filter (fun K => sources ends K = ({o, x} : Finset W)))) := by
    rw [Finset.card_sigma]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext m; simp only [Finset.mem_filter, Finset.mem_powerset]; tauto
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_powerset] at hm
      rw [gc50_E_eq_oxCount_of_all_conn ends m hox hog hxg hm.2.2.1 hm.2.2.2.2]
  rw [hstep1]
  
  rw [gc50_reindex_by_oxCurrent ends o x ({o, x, y, g} : Finset W) ({y, g} : Finset W)
    (gc50_sd_oxyg_ox hoy hog hxy hxg)
    (G := fun m => connK ends m o x ∧ connK ends m o y ∧ connK ends m o g)]
  apply Finset.sum_congr rfl
  intro K hK
  rfl


end Abstract
end StatMech.Walls
