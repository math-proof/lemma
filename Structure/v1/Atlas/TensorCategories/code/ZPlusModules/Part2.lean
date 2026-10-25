/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ZPlusModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Abbrev.v1.Atlas.TensorCategories.code.ZPlusModules
set_option maxHeartbeats 800000


/-- A `ℤ_+`-ring with finite index set `ι`: nonnegative integer structure constants
`N i j k`, a unit subset `I₀`, and the unitality and associativity axioms expressed
with ordinary finite sums. -/
structure ZPlusRing (ι : Type*) [DecidableEq ι] [Fintype ι] where
  N : ι → ι → ι → ℕ
  I₀ : Finset ι
  unit_mul : ∀ j k, ∑ s ∈ I₀, N s j k = if j = k then 1 else 0
  mul_unit : ∀ i k, ∑ s ∈ I₀, N i s k = if i = k then 1 else 0
  assoc : ∀ i j k l, ∑ m : ι, N i j m * N m k l = ∑ m : ι, N j k m * N i m l

