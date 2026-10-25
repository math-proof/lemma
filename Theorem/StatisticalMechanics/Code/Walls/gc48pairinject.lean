/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc48pairinject.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc47aggregate.Part4
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
  exists_conn_set sources_symmDiff path_exists mem_sources)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc48_pairInjection_of_pairCount_le (ends : ι → Sym2 W) (o x y g : W)
    (hcard : #(gc47_LHSpairs ends o x y g) ≤ #(gc47_RHSpairs ends o x y g)) :
    gc47_PairInjection ends o x y g := by
  rcases Finset.eq_empty_or_nonempty (gc47_LHSpairs ends o x y g) with hLempty | hLne
  · 
    refine ⟨id, ?_, ?_⟩
    · intro p hp; rw [hLempty] at hp; exact absurd hp (Finset.notMem_empty p)
    · intro a ha; rw [Finset.mem_coe, hLempty] at ha; exact absurd ha (Finset.notMem_empty a)
  · 
    have hRne : (gc47_RHSpairs ends o x y g).Nonempty := by
      rw [← Finset.card_pos]
      exact lt_of_lt_of_le (Finset.card_pos.mpr hLne) hcard
    obtain ⟨r₀, hr₀⟩ := hRne
    
    have hcardcoe : Fintype.card (gc47_LHSpairs ends o x y g) ≤ #(gc47_RHSpairs ends o x y g) := by
      rw [Fintype.card_coe]; exact hcard
    obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset hcardcoe
    
    refine ⟨fun p => if h : p ∈ gc47_LHSpairs ends o x y g then f ⟨p, h⟩ else r₀, ?_, ?_⟩
    · 
      intro p hp
      simp only [dif_pos hp]
      exact hf (Set.mem_range_self _)
    · 
      intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      simp only [dif_pos ha, dif_pos hb] at hab
      have := f.injective hab
      exact congrArg Subtype.val this


theorem gc48_pairInjection_of_EMassResidue (ends : ι → Sym2 W) (o x y g : W)
    (h : gc42_EMassResidue ends o x y g) :
    gc47_PairInjection ends o x y g :=
  gc48_pairInjection_of_pairCount_le ends o x y g
    ((gc47_EMassResidue_iff_pairCount_le ends o x y g).mp h)


theorem gc48_pairInjection_iff_EMassResidue (ends : ι → Sym2 W) (o x y g : W) :
    gc47_PairInjection ends o x y g ↔ gc42_EMassResidue ends o x y g :=
  ⟨gc47_EMassResidue_of_pairInjection ends o x y g,
    gc48_pairInjection_of_EMassResidue ends o x y g⟩


theorem gc48_pairInjection_iff_pairCount_le (ends : ι → Sym2 W) (o x y g : W) :
    gc47_PairInjection ends o x y g
      ↔ #(gc47_LHSpairs ends o x y g) ≤ #(gc47_RHSpairs ends o x y g) :=
  (gc48_pairInjection_iff_EMassResidue ends o x y g).trans
    (gc47_EMassResidue_iff_pairCount_le ends o x y g)


end Abstract
end StatMech.Walls
