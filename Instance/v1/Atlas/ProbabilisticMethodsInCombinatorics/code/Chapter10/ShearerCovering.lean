/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/ShearerCovering.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Card
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.ShearerCovering

@[expose] public section

set_option maxHeartbeats 1600000

open Finset SimpleGraph


namespace BipartiteDoubleCover

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Decidability of the independence predicate on finsets when adjacency in $G$ is decidable. -/
instance instDecIsIndepFinset {W : Type*} [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] : DecidablePred (IsIndepFinset G) := by
  intro S; unfold IsIndepFinset; exact inferInstance

end BipartiteDoubleCover
