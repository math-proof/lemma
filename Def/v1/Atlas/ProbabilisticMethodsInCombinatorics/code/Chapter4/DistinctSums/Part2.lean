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
import Abbrev.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter4.DistinctSums
set_option maxHeartbeats 400000


namespace HarperIsoperimetric

/-- Two vertices of the hypercube are adjacent if their Hamming distance is $1$,
    i.e. they differ in exactly one coordinate. -/
def Hypercube.Adjacent {k : ℕ} (x y : Hypercube k) : Prop :=
  hammingDist x y = 1

end HarperIsoperimetric
