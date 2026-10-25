/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Sidorenko.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.SuccPred
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.Sidorenko
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
