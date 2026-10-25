/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/HopcroftKarp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Matching.ShortestAugPathPhase.Part2
open SimpleGraph


namespace SimpleGraph

universe u w

structure HopcroftKarpExecution {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  numPhases : ℕ
  matching : Fin (numPhases + 1) → G.Subgraph
  isMatching : ∀ i, (matching i).IsMatching
  isFinalMaximum : ∀ M' : G.Subgraph, M'.IsMatching →
    M'.edgeSet.ncard ≤ (matching ⟨numPhases, Nat.lt_succ_of_le le_rfl⟩).edgeSet.ncard
  size_strictly_increases : ∀ i : Fin numPhases,
    (matching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).edgeSet.ncard <
    (matching ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩).edgeSet.ncard
  shortestLen : Fin numPhases → ℕ
  shortestLen_spec : ∀ i : Fin numPhases,
    shortestAugPathLength G (matching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) =
      ↑(shortestLen i)
  paths : (i : Fin numPhases) →
    VertexDisjointAugPaths.{u, w} G (matching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) (shortestLen i)
  paths_maximal : ∀ i : Fin numPhases, (paths i).IsMaximal
  isAugmentation : ∀ i : Fin numPhases,
    IsAugmentationAlongPaths
      (matching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (matching ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (paths i)

end SimpleGraph
