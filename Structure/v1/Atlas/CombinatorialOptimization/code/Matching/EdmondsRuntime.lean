/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/EdmondsRuntime.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Matching.EdmondsProgress
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Matching.EdmondsProgress
open SimpleGraph


namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure EdmondsExecution (G : SimpleGraph V) where
  numPhases : ℕ
  matching : Fin (numPhases + 1) → G.Subgraph
  isMatching : ∀ i, (matching i).IsMatching
  size_increases_by_one : ∀ i : Fin numPhases,
    (matching ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩).edgeSet.ncard =
    (matching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).edgeSet.ncard + 1
  isFinalMaximum : Subgraph.IsMaxMatching
    (matching ⟨numPhases, Nat.lt_succ_of_le le_rfl⟩)

structure EdmondsPhaseDetail (G : SimpleGraph V) where
  numContractions : ℕ
  vertexCounts : Fin (numContractions + 1) → ℕ
  initial_le : vertexCounts ⟨0, Nat.zero_lt_succ _⟩ ≤ Fintype.card V
  contraction_reduces : ∀ i : Fin numContractions,
    vertexCounts ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ + 2 ≤
    vertexCounts ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

end SimpleGraph
