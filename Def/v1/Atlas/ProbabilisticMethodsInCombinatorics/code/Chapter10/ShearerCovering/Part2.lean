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
public import Instance.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.ShearerCovering

@[expose] public section

set_option maxHeartbeats 1600000

open Finset SimpleGraph


namespace BipartiteDoubleCover

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The finset of all independent vertex sets of $G$. -/
def indepSets {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] : Finset (Finset W) :=
  Finset.univ.filter (IsIndepFinset G)

/-- The number of independent vertex sets of $G$, denoted $i(G)$. -/
def numIndepSets {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] : ℕ :=
  (indepSets G).card

end BipartiteDoubleCover
