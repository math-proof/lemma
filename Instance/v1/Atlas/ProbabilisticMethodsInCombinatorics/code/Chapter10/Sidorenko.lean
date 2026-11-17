/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Sidorenko.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.SuccPred
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.Sidorenko

@[expose] public section

set_option maxHeartbeats 400000

open SimpleGraph Finset BigOperators


namespace BlakleyRoy

/-- Decidability of adjacency in the path graph $P_4$ on four vertices. -/
instance pathGraph4_decidableAdj : DecidableRel (SimpleGraph.pathGraph 4).Adj := by
  intro a b
  unfold SimpleGraph.pathGraph
  rw [SimpleGraph.hasse_adj, Fin.covBy_iff, Fin.covBy_iff,
      Nat.covBy_iff_add_one_eq, Nat.covBy_iff_add_one_eq]
  exact instDecidableOr

end BlakleyRoy
