/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bftfinetrif.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bcvcutvertex.Part3
import Theorem.StatisticalMechanics.Code.Walls.bararmray
import Theorem.StatisticalMechanics.Code.Walls.bfctfinitecount.Part4
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bft_boxAround_zero (y : Site d) : bc61_boxAround d 0 y = {y} := by
  ext x
  rw [bc61_mem_boxAround, mem_box, Finset.mem_singleton]
  constructor
  · intro h
    funext i
    have hi := h i
    rw [Pi.sub_apply] at hi
    omega
  · intro h; subst h; intro i; simp


theorem bft_contractedLattice_zero (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    bc67_contractedLattice ω 0 x = bkg_deleteVertex (openSubgraph d ω) x := by
  apply SimpleGraph.ext
  ext a b
  rw [bc67_contractedLattice_adj, openSubgraph_adj, bkg_deleteVertex_adj, openSubgraph_adj]
  rw [bft_boxAround_zero]
  constructor
  · rintro ⟨hlat, hopen⟩
    unfold removeSites at hopen
    by_cases hx : ∃ t ∈ ({x} : Finset (Site d)), t ∈ s(a, b)
    · rw [if_pos hx] at hopen; exact absurd hopen (by simp)
    · rw [if_neg hx] at hopen
      have hax : a ≠ x := by
        intro h; exact hx ⟨x, Finset.mem_singleton_self x, by rw [Sym2.mem_iff]; left; exact h.symm⟩
      have hbx : b ≠ x := by
        intro h; exact hx ⟨x, Finset.mem_singleton_self x, by rw [Sym2.mem_iff]; right; exact h.symm⟩
      exact ⟨⟨hlat, hopen⟩, hax, hbx⟩
  · rintro ⟨⟨hlat, hopen⟩, hax, hbx⟩
    refine ⟨hlat, ?_⟩
    unfold removeSites
    have hx : ¬ ∃ t ∈ ({x} : Finset (Site d)), t ∈ s(a, b) := by
      rintro ⟨t, ht, htmem⟩
      rw [Finset.mem_singleton] at ht; subst ht
      rw [Sym2.mem_iff] at htmem
      rcases htmem with h | h
      · exact hax h.symm
      · exact hbx h.symm
    rw [if_neg hx]; exact hopen


theorem bft_deleteVertex_le (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    bkg_deleteVertex (openSubgraph d ω) x ≤ openSubgraph d ω := by
  intro a b hab; exact hab.1


end StatMech.Walls
