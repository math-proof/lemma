/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutsupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Def.StatisticalMechanics.Code.Walls.gc8cutsupport.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 800000


namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc8_cutSupportDecomp_of_closedCut (S : Finset V) (hcut : acwClosedCut G S)
    (n₁ n₂ : Ising.Current V) :
    gc8_cutSupportDecomp G S n₁ n₂ := by
  refine ⟨fun e he => gc8_cut_no_crossing G S hcut e he, fun e he => ?_, ?_, ?_⟩
  · exact ⟨gc8_current_split G S hcut n₁ e he, gc8_current_split G S hcut n₂ e he⟩
  · exact gc8_sources_internal_eq G S hcut n₁
  · exact gc8_sources_internal_eq G S hcut n₂


theorem gc8_current_decomp (S : Finset V) (hcut : acwClosedCut G S) (n : Ising.Current V) :
    (∀ e ∈ G.edgeFinset, ¬ gc8Crosses S e)
      ∧ (∀ e ∈ G.edgeFinset,
          n e = acwRestrict (acwInternal S) n e + acwRestrict (acwInternal Sᶜ) n e)
      ∧ Sharpness.sources G (acwRestrict (acwInternal S) n) = S ∩ Sharpness.sources G n
      ∧ Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n) = Sᶜ ∩ Sharpness.sources G n
      ∧ Disjoint (Sharpness.sources G (acwRestrict (acwInternal S) n))
          (Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n)) := by
  refine ⟨fun e he => gc8_cut_no_crossing G S hcut e he,
    fun e he => gc8_current_split G S hcut n e he,
    gc8_sources_internal_eq G S hcut n,
    gc8_sources_external_eq G S hcut n, ?_⟩
  exact (gc8_sources_split G S hcut n).2


theorem gc8_closedCut_bot (S : Finset V) :
    acwClosedCut (⊥ : SimpleGraph V) S := by
  intro e he
  simp only [SimpleGraph.edgeFinset, Set.mem_toFinset, SimpleGraph.edgeSet_bot,
    Set.mem_empty_iff_false] at he


theorem gc8_cutSupportDecomp_bot (S : Finset V) (n₁ n₂ : Ising.Current V) :
    gc8_cutSupportDecomp (⊥ : SimpleGraph V) S n₁ n₂ :=
  gc8_cutSupportDecomp_of_closedCut (⊥ : SimpleGraph V) S (gc8_closedCut_bot S) n₁ n₂

end StatMech.Walls
