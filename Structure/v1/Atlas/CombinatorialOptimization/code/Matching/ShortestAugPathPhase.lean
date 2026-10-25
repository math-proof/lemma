/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/ShortestAugPathPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Matching.Berge
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Matching.Berge
import Def.v1.Atlas.CombinatorialOptimization.code.Matching.ShortestAugPathPhase
open SimpleGraph


namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

structure VertexDisjointAugPaths (G : SimpleGraph V) (M : G.Subgraph) (k : ℕ) where
  ι : Type*
  src : ι → V
  tgt : ι → V
  path : (i : ι) → G.Walk (src i) (tgt i)
  isAug : ∀ i, (path i).IsAugmentingPath M
  hasLen : ∀ i, (path i).length = k
  disjoint : ∀ i j, i ≠ j →
    List.Disjoint ((path i).support) ((path j).support)

end SimpleGraph
