/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh5currentrep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gh4eq22.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc85bthreereplicaswitch.Part3
import Def.StatisticalMechanics.Code.Walls.gh5currentrep
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
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent

open StatMech.Walls.GhcEqGap

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]


theorem gh5_compMass_eq_complMass (ends : ι → Sym2 W) (m : Finset ι) (V₁ V₂ : Finset W) (u : W)
    (A : Finset ι) (hAm : A ⊆ m) :
    gh4_compMass ends m V₁ V₂ u A = gh5_complMass ends m V₁ V₂ u A := by
  classical
  unfold gh4_compMass gh5_complMass
  apply Finset.card_bij (fun KK _ => (KK.1 \ A, KK.2))
  · 
    rintro ⟨K₁, K₂⟩ hKK
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hKK ⊢
    obtain ⟨⟨hK₁m, hK₂m⟩, hdis, hV₁, hV₂, hcomp⟩ := hKK
    
    have hAK₁ : A ⊆ K₁ := hcomp ▸ gh4_bondCompOf_subset ends K₁ u
    
    have hunion : A ∪ (K₁ \ A) = K₁ := by
      rw [Finset.union_sdiff_of_subset hAK₁]
    refine ⟨⟨?_, ?_⟩, ?_, ?_, hV₂, ?_⟩
    · 
      exact Finset.sdiff_subset_sdiff hK₁m (le_refl A)
    · 
      intro a ha
      rw [Finset.mem_sdiff]
      refine ⟨hK₂m ha, ?_⟩
      intro haA
      exact (Finset.disjoint_left.1 hdis) (hAK₁ haA) ha
    · 
      exact Finset.disjoint_of_subset_left Finset.sdiff_subset hdis
    · 
      rw [hunion]; exact hV₁
    · 
      rw [hunion]; exact hcomp
  · 
    rintro ⟨K₁, K₂⟩ hKK ⟨L₁, L₂⟩ hLL heq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hKK hLL
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    
    have hAK₁ : A ⊆ K₁ := hKK.2.2.2.2 ▸ gh4_bondCompOf_subset ends K₁ u
    have hAL₁ : A ⊆ L₁ := hLL.2.2.2.2 ▸ gh4_bondCompOf_subset ends L₁ u
    have : K₁ = L₁ := by
      rw [← Finset.union_sdiff_of_subset hAK₁, ← Finset.union_sdiff_of_subset hAL₁, h1]
    rw [Prod.mk.injEq]; exact ⟨this, h2⟩
  · 
    rintro ⟨K₁', K₂'⟩ hKK
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hKK
    obtain ⟨⟨hK₁m, hK₂m⟩, hdis, hV₁, hV₂, hcomp⟩ := hKK
    
    have hK₁A : Disjoint A K₁' := by
      rw [Finset.disjoint_left]
      intro a haA haK
      exact (Finset.mem_sdiff.1 (hK₁m haK)).2 haA
    have hK₂A : Disjoint A K₂' := by
      rw [Finset.disjoint_left]
      intro a haA haK
      exact (Finset.mem_sdiff.1 (hK₂m haK)).2 haA
    refine ⟨(A ∪ K₁', K₂'), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
      refine ⟨⟨?_, ?_⟩, ?_, hV₁, hV₂, hcomp⟩
      · 
        exact Finset.union_subset hAm (hK₁m.trans Finset.sdiff_subset)
      · 
        exact hK₂m.trans Finset.sdiff_subset
      · 
        rw [Finset.disjoint_union_left]
        exact ⟨hK₂A, Finset.disjoint_of_subset_right (le_refl K₂') hdis⟩
    · 
      simp only [Prod.mk.injEq, and_true]
      
      rw [Finset.union_sdiff_cancel_left hK₁A]


end StatMech.Walls
