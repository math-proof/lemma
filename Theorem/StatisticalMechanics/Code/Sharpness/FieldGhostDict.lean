/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FieldGhostDict.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Def.StatisticalMechanics.Code.Sharpness.FieldGhostDict
open Finset SimpleGraph
open scoped symmDiff
open StatMech StatMech.Ising StatMech.Sharpness

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

namespace FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem withGhost_edgeFinset_eq : (withGhost G).edgeFinset = origEdges G ∪ ghostEdges V := by
  ext e
  rw [mem_edgeFinset, Finset.mem_union]
  induction e with
  | h a b =>
    simp only [origEdges, ghostEdges, Finset.mem_image, mem_edgeFinset, SimpleGraph.mem_edgeSet,
      mem_univ, true_and]
    rcases a with _ | x <;> rcases b with _ | y
    · constructor
      · intro h; exact absurd h (by trivial)
      · rintro (⟨e1, _, he⟩ | ⟨x, hx⟩)
        · induction e1 with | h c d => rw [Sym2.map_mk, Sym2.eq_iff] at he; simp_all
        · rw [Sym2.eq_iff] at hx; simp_all
    · constructor
      · intro _; right; exact ⟨y, by rw [Sym2.eq_swap]⟩
      · intro _; show (withGhost G).Adj none (some y); simp only [withGhost]
    · constructor
      · intro _; right; exact ⟨x, rfl⟩
      · intro _; show (withGhost G).Adj (some x) none; simp only [withGhost]
    · rw [withGhost_adj_some_some]
      constructor
      · intro h; left; exact ⟨s(x, y), h, by rw [Sym2.map_mk]⟩
      · rintro (⟨e1, he1, he⟩ | ⟨z, hz⟩)
        · induction e1 with
          | h c d => rw [Sym2.map_mk, Sym2.eq_iff] at he
                     rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
                     · rw [Option.some_inj.mp h1, Option.some_inj.mp h2] at he1; exact he1
                     · rw [Option.some_inj.mp h1, Option.some_inj.mp h2] at he1; exact he1.symm
        · rw [Sym2.eq_iff] at hz; simp_all


theorem disjoint_orig_ghost : Disjoint (origEdges G) (ghostEdges V) := by
  rw [Finset.disjoint_left]
  intro e he hg
  simp only [origEdges, ghostEdges, Finset.mem_image, mem_edgeFinset, mem_univ, true_and] at he hg
  obtain ⟨e1, he1, rfl⟩ := he
  obtain ⟨x, hx⟩ := hg
  induction e1 with
  | h a b => rw [Sym2.map_mk, Sym2.eq_iff] at hx; rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all


end FieldGhostDict
end Sharpness
end StatMech
