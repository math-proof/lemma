/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/SumFree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section

set_option maxHeartbeats 400000

open Finset


namespace SumFree

/-- A subset $S \subseteq \mathbb{Z}$ is sum-free if no two elements (possibly equal)
sum to a third, i.e., $a + b \neq c$ for all $a, b, c \in S$. -/
def IsSumFree (S : Finset ℤ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a + b ≠ c

end SumFree
