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
import Instance.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.Sidorenko
set_option maxHeartbeats 400000

open SimpleGraph Finset BigOperators


namespace BlakleyRoy

/-- Number of length-3 walks in $G$ counted as $\sum_b \deg(b) \sum_{c \sim b} \deg(c)$, used
to express homomorphism counts from $P_4$ into $G$. -/
noncomputable def walkCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ∑ b : V, G.degree b * ∑ c ∈ G.neighborFinset b, G.degree c

end BlakleyRoy
