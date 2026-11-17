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
public import Instance.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.KahnZhao

@[expose] public section

set_option maxHeartbeats 400000


namespace SimpleGraph

/-- $i(G)$: the number of independent sets in a finite simple graph $G$, counting the
empty set. -/
noncomputable def numIndSets {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun s : Finset V =>
    ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬G.Adj u v)).card

end SimpleGraph
