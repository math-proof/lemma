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

set_option maxHeartbeats 400000

open SimpleGraph Finset BigOperators

namespace Sidorenko

/-- The homomorphism density $t(F,G) = \mathrm{hom}(F,G) / |W|^{|V|}$ of a graph homomorphism
from $F$ into $G$, where $V = V(F)$ and $W = V(G)$. -/
noncomputable def homDensity {V : Type*} {W : Type*}
    (F : SimpleGraph V) (G : SimpleGraph W) : ℝ :=
  (Nat.card (F →g G) : ℝ) / (Nat.card W : ℝ) ^ (Nat.card V)

end Sidorenko


/-- The Sidorenko conjecture (Conjecture 10.3.2): for any bipartite graph $F$ and any graph $G$,
the homomorphism density satisfies $t(F,G) \ge t(K_2,G)^{e(F)}$. -/
namespace BlakleyRoy

/-- Decidability of adjacency in the path graph $P_4$ on four vertices. -/
instance pathGraph4_decidableAdj : DecidableRel (SimpleGraph.pathGraph 4).Adj := by
  intro a b
  unfold SimpleGraph.pathGraph
  rw [SimpleGraph.hasse_adj, Fin.covBy_iff, Fin.covBy_iff,
      Nat.covBy_iff_add_one_eq, Nat.covBy_iff_add_one_eq]
  exact instDecidableOr

/-- Number of length-3 walks in $G$ counted as $\sum_b \deg(b) \sum_{c \sim b} \deg(c)$, used
to express homomorphism counts from $P_4$ into $G$. -/
noncomputable def walkCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ∑ b : V, G.degree b * ∑ c ∈ G.neighborFinset b, G.degree c
