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

@[expose] public section

set_option maxHeartbeats 400000

open SimpleGraph Finset BigOperators


namespace Sidorenko

/-- The homomorphism density $t(F,G) = \mathrm{hom}(F,G) / |W|^{|V|}$ of a graph homomorphism
from $F$ into $G$, where $V = V(F)$ and $W = V(G)$. -/
noncomputable def homDensity {V : Type*} {W : Type*}
    (F : SimpleGraph V) (G : SimpleGraph W) : ℝ :=
  (Nat.card (F →g G) : ℝ) / (Nat.card W : ℝ) ^ (Nat.card V)

end Sidorenko
