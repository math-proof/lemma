/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/DistinctSums.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter4.DistinctSums
set_option maxHeartbeats 400000


namespace HarperIsoperimetric

/-- The $k$-dimensional Boolean hypercube $\{0,1\}^k$, represented as functions
    $\mathrm{Fin}\, k \to \mathrm{Bool}$. -/
abbrev Hypercube (k : ℕ) := Fin k → Bool

end HarperIsoperimetric
