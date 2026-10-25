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
