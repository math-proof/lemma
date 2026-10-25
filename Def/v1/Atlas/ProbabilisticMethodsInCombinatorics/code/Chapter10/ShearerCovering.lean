/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/ShearerCovering.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
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
