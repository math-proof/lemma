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
import Def.StatisticalMechanics.Code.Sharpness.BackbonePropsFull.Part2
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

open StatMech.Ising (bond)

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp]
theorem shb_mem_backboneSet (n : Current V) (x y : V) (ω : G.Path x y) :
    ω ∈ shb_backboneSet G n x y ↔ shb_IsBackboneOf G n x y ω := by
  unfold shb_backboneSet; simp [Finset.mem_filter]


theorem shb_isBackbonePath_mem_backboneSet (n : Current V) (x y : V)
    (p : IsBackbonePath G n x y) :
    (⟨p.1.mapLe (oddSubgraph_le G n), p.2.mapLe (oddSubgraph_le G n)⟩ : G.Path x y)
      ∈ shb_backboneSet G n x y := by
  rw [shb_mem_backboneSet]
  intro e he
  rw [Walk.edges_mapLe_eq_edges] at he
  exact isBackbonePath_edge_odd G p he


end Sharpness
end StatMech
