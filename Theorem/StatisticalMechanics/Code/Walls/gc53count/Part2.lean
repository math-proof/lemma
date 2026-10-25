/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc53count.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc52switchinj.Part2
import Def.StatisticalMechanics.Code.Walls.gc53count
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


theorem gc53_Rblock_card_eq_cosetGate (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hyg : y ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    {P₀ : Finset ι} (hP₀sub : P₀ ⊆ univ \ K) (hP₀src : sources ends P₀ = ({y, g} : Finset W)) :
    #(gc51_RblockSet ends K o x y g) = #(gc53_cosetGateBlock ends K P₀ o x g) := by
  rw [gc53_Rblock_eq_gateBlock ends hnd K hox hyg hKsrc, gc53_cosetGateBlock]
  
  rw [show ((univ \ K).powerset.filter
        (fun Q => sources ends Q = ({y, g} : Finset W) ∧ connK ends (K ∪ Q) x g))
      = ((univ \ K).powerset.filter
          (fun L => sources ends L = (∅ : Finset W) ∧ connK ends (K ∪ (L ∆ P₀)) x g)).image
            (fun L => L ∆ P₀) from ?_]
  · rw [Finset.card_image_of_injOn]
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at ha hb
    simp only at hab
    have : (a ∆ P₀) ∆ P₀ = (b ∆ P₀) ∆ P₀ := by rw [hab]
    rwa [symmDiff_symmDiff_cancel_right, symmDiff_symmDiff_cancel_right] at this
  · ext Q
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hQV, hQsrc, hgate⟩
      
      refine ⟨Q ∆ P₀, ⟨?_, ?_, ?_⟩, ?_⟩
      · 
        intro i hi
        rw [Finset.mem_symmDiff] at hi
        rcases hi with ⟨h, _⟩ | ⟨h, _⟩
        · exact hQV h
        · exact hP₀sub h
      · 
        rw [sources_symmDiff, hQsrc, hP₀src, symmDiff_self]; rfl
      · 
        rwa [symmDiff_symmDiff_cancel_right]
      · 
        rw [symmDiff_symmDiff_cancel_right]
    · rintro ⟨L, ⟨hLV, hLsrc, hgate⟩, rfl⟩
      refine ⟨?_, ?_, hgate⟩
      · 
        intro i hi
        rw [Finset.mem_symmDiff] at hi
        rcases hi with ⟨h, _⟩ | ⟨h, _⟩
        · exact hLV h
        · exact hP₀sub h
      · 
        rw [sources_symmDiff, hLsrc, hP₀src]; simp


end Abstract
end StatMech.Walls
