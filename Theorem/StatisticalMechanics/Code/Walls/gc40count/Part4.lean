/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Walls.gc39threereplica.Part3
import Def.StatisticalMechanics.Code.Walls.gc40count.Part4
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


theorem gc40_countIneq_of_EWeighted (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hres : gc40_EWeightedCountResidue ends o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g := by
  rw [gc40_countIneq_iff, gc40_NR_eq_Esum ends hnd hox hoy hog hxy hxg hyg huniv,
    gc40_NL_eq_sum_inner ends huniv]
  exact hres


theorem gc40_L_le_E (ends : ι → Sym2 W) (S₁ : Finset ι) (o x y g : W) :
    gc40_L ends S₁ o x y g ≤ gc40_E ends (univ \ S₁) := by
  rw [gc40_L, gc40_E]
  apply Finset.card_le_card
  intro S₂ hS₂
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS₂ ⊢
  exact ⟨hS₂.1, hS₂.2.1⟩


theorem gc40_NRsummand_le_E (ends : ι → Sym2 W) (S₁ : Finset ι) {y g : W} :
    (if connK ends (univ \ S₁) y g then gc40_E ends (univ \ S₁) else 0) ≤ gc40_E ends (univ \ S₁) := by
  by_cases h : connK ends (univ \ S₁) y g
  · rw [if_pos h]
  · rw [if_neg h]; exact Nat.zero_le _

end Abstract
end StatMech.Walls
