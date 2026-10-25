/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/ShortestAugPathPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Matching.Berge
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Matching.Berge
import Structure.v1.Atlas.CombinatorialOptimization.code.Matching.ShortestAugPathPhase
open SimpleGraph


namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def VertexDisjointAugPaths.IsMaximal {G : SimpleGraph V} {M : G.Subgraph} {k : ℕ}
    (paths : VertexDisjointAugPaths G M k) : Prop :=
  ∀ (u v : V) (p : G.Walk u v),
    p.IsAugmentingPath M → p.length = k →
    ∃ i, ¬ List.Disjoint p.support ((paths.path i).support)

def IsAugmentationAlongPaths {G : SimpleGraph V} (M M' : G.Subgraph) {k : ℕ}
    (paths : VertexDisjointAugPaths G M k) : Prop :=
  M'.IsMatching ∧
  (∀ e ∈ M'.edgeSet, e ∉ M.edgeSet →
    ∃ i, e ∈ (paths.path i).edges.toFinset) ∧
  (∀ e ∈ M.edgeSet, e ∉ M'.edgeSet →
    ∃ i, e ∈ (paths.path i).edges.toFinset) ∧
  (∀ v : V, (∀ i, v ∉ (paths.path i).support) →
    (v ∈ M.verts ↔ v ∈ M'.verts))

end SimpleGraph
