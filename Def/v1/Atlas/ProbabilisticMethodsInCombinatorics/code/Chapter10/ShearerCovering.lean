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

@[expose] public section

set_option maxHeartbeats 1600000

open Finset SimpleGraph


namespace BipartiteDoubleCover

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finset $S$ of vertices of $G$ is independent if no two distinct vertices in $S$ are
adjacent. -/
def IsIndepFinset {W : Type*} [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (S : Finset W) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v

end BipartiteDoubleCover
