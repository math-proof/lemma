/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Walls.gc39threereplica.Part3
import Def.StatisticalMechanics.Code.Walls.gc40count.Part2
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


theorem gc40_countIneq_iff (ends : ι → Sym2 W) (o x y g : W) :
    gc39_ThreeColouringCountIneq ends o x y g ↔ gc40_NR ends o x y g ≤ gc40_NL ends o x y g := by
  rfl


theorem gc40_NR_eq_Esum (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W)) :
    gc40_NR ends o x y g
      = ∑ S₁ ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, g} : Finset W)),
          (if connK ends (univ \ S₁) y g then gc40_E ends (univ \ S₁) else 0) := by
  rw [gc40_NR]
  rw [gc40_pairCount_reindex (P := fun S => sources ends S = ({o, g} : Finset W))
    (Q := fun S₁ S₂ => sources ends S₂ = ({x, g} : Finset W)
      ∧ sources ends ((univ \ S₁) \ S₂) = ({y, g} : Finset W))]
  apply Finset.sum_congr rfl
  intro S₁ hS₁
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS₁
  
  have hMsrc : sources ends (univ \ S₁) = ({x, y} : Finset W) := by
    rw [gc40_sources_compl, huniv, hS₁.2, gc40_sd_oxyg_og hox hoy hog hxy hxg hyg]
  rw [gc40_inner_drop_third ends (univ \ S₁) hMsrc hxg hyg hxy]
  rw [gc40_inner_count_collapse ends (univ \ S₁)
    (fun i _ => hnd i) hMsrc hxg hyg hxy]


end Abstract
end StatMech.Walls
