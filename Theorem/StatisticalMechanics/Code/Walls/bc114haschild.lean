/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc114haschild.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc113boundaryforest.Part6
open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]


variable {G : SimpleGraph V}


theorem bc114_internal_two_neighbours (F : SimpleGraph V) {s t : V} (p : F.Walk s t)
    (hp : p.IsPath) {i : ℕ} (hi0 : 0 < i) (hilt : i < p.length) :
    F.Adj (p.getVert i) (p.getVert (i - 1)) ∧ F.Adj (p.getVert i) (p.getVert (i + 1)) ∧
      p.getVert (i - 1) ≠ p.getVert (i + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · 
    have hprev : (i - 1) < p.length := by omega
    have hadj : F.Adj (p.getVert (i - 1)) (p.getVert ((i - 1) + 1)) := p.adj_getVert_succ hprev
    have : (i - 1) + 1 = i := by omega
    rw [this] at hadj
    exact hadj.symm
  · exact p.adj_getVert_succ hilt
  · 
    have hinj := hp.getVert_injOn
    intro heq
    have h1 : (i - 1) ∈ {j | j ≤ p.length} := by simp; omega
    have h2 : (i + 1) ∈ {j | j ≤ p.length} := by simp; omega
    have := hinj h1 h2 heq
    omega


theorem bc114_internal_degree_ge_two (F : SimpleGraph V) [DecidableRel F.Adj] {s t : V}
    (p : F.Walk s t) (hp : p.IsPath) {i : ℕ} (hi0 : 0 < i) (hilt : i < p.length) :
    2 ≤ F.degree (p.getVert i) := by
  obtain ⟨hadj1, hadj2, hne⟩ := bc114_internal_two_neighbours F p hp hi0 hilt
  have hsub : {p.getVert (i - 1), p.getVert (i + 1)} ⊆ F.neighborFinset (p.getVert i) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [SimpleGraph.mem_neighborFinset]
    rcases hz with rfl | rfl
    · exact hadj1
    · exact hadj2
  calc 2 = ({p.getVert (i - 1), p.getVert (i + 1)} : Finset V).card := by
          rw [Finset.card_pair hne]
    _ ≤ (F.neighborFinset (p.getVert i)).card := Finset.card_le_card hsub
    _ = F.degree (p.getVert i) := SimpleGraph.card_neighborFinset_eq_degree _ _


end StatMech.Walls
