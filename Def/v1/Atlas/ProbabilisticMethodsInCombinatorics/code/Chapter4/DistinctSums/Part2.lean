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
public import Abbrev.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter4.DistinctSums

@[expose] public section

set_option maxHeartbeats 400000


namespace HarperIsoperimetric

/-- Two vertices of the hypercube are adjacent if their Hamming distance is $1$,
    i.e. they differ in exactly one coordinate. -/
def Hypercube.Adjacent {k : ℕ} (x y : Hypercube k) : Prop :=
  hammingDist x y = 1

end HarperIsoperimetric
