/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePropsFull
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

open StatMech.Ising (bond)

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def shb_backboneOf_imp_isBackbonePath (n : Current V) (x y : V) (ω : G.Path x y)
    (h : shb_IsBackboneOf G n x y ω) : IsBackbonePath G n x y := by
  refine ⟨ω.1.transfer (oddSubgraph G n) ?_, ω.2.transfer _⟩
  intro e he
  have hG : e ∈ G.edgeSet := ω.1.edges_subset_edgeSet he
  have hodd : Odd (n e) := h e he
  revert hG hodd
  refine Sym2.ind (fun a b => ?_) e
  intro hG hodd
  rw [SimpleGraph.mem_edgeSet] at hG ⊢
  exact ⟨hG, hodd⟩


end Sharpness
end StatMech
