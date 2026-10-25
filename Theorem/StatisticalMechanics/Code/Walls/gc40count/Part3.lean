/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Walls.gc39threereplica.Part3
import Def.StatisticalMechanics.Code.Walls.gc40count.Part3
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


theorem gc40_NL_eq_sum_inner (ends : ι → Sym2 W) {o x y g : W}
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W)) :
    gc40_NL ends o x y g
      = ∑ S₁ ∈ (univ : Finset ι).powerset.filter
          (fun S => sources ends S = ({o, x, y, g} : Finset W)), gc40_L ends S₁ o x y g := by
  rw [gc40_NL]
  rw [gc40_pairCount_reindex (P := fun S => sources ends S = ({o, x, y, g} : Finset W))
    (Q := fun S₁ S₂ => sources ends S₂ = (∅ : Finset W)
      ∧ sources ends ((univ \ S₁) \ S₂) = (∅ : Finset W)
      ∧ connK ends (S₁ ∪ S₂) o x ∧ connK ends (S₁ ∪ S₂) o y ∧ connK ends (S₁ ∪ S₂) o g)]
  apply Finset.sum_congr rfl
  intro S₁ hS₁
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS₁
  
  have hMsrc : sources ends (univ \ S₁) = (∅ : Finset W) := by
    rw [gc40_sources_compl, huniv, hS₁.2, symmDiff_self]; rfl
  rw [gc40_L]
  apply congrArg
  apply Finset.filter_congr
  intro S₂ hS₂
  simp only [Finset.mem_powerset] at hS₂
  
  constructor
  · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    refine ⟨h1, ?_, h3⟩
    have hcompl : (univ \ S₁) \ S₂ = (univ \ S₁) ∆ S₂ := (symmDiff_of_ge hS₂).symm
    rw [hcompl, sources_symmDiff, hMsrc, h1, symmDiff_self]; rfl


end Abstract
end StatMech.Walls
