/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/DistinctSums.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter4.DistinctSums
@[expose] public section

set_option maxHeartbeats 400000


namespace HarperIsoperimetric

/-- The $k$-dimensional Boolean hypercube $\{0,1\}^k$, represented as functions
    $\mathrm{Fin}\, k \to \mathrm{Bool}$. -/
abbrev Hypercube (k : ℕ) := Fin k → Bool

end HarperIsoperimetric
