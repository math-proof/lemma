/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/KahnZhao.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

set_option maxHeartbeats 400000


namespace SimpleGraph

/-- Decidability of adjacency in the complete bipartite graph on $V \sqcup W$. -/
instance completeBipartiteGraph.instDecidableRel (V W : Type*) [DecidableEq V] [DecidableEq W] :
    DecidableRel (completeBipartiteGraph V W).Adj := by
  intro x y
  simp only [completeBipartiteGraph]
  exact instDecidableOr

end SimpleGraph
