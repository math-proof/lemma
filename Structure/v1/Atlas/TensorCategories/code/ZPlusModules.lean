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
set_option maxHeartbeats 800000


/-- A `ℤ_+`-ring (general version, not requiring `ι` to be finite): a set `ι` of
distinguished basis elements with nonnegative integer structure constants `N i j k`
satisfying unitality and associativity, and with finite multiplicative support. -/
structure ZPlusRingGen (ι : Type*) [DecidableEq ι] where
  N : ι → ι → ι → ℕ
  I₀ : Finset ι
  finite_support : ∀ i j, Set.Finite {k | N i j k ≠ 0}
  unit_mul : ∀ j k, ∑ s ∈ I₀, N s j k = if j = k then 1 else 0
  mul_unit : ∀ i k, ∑ s ∈ I₀, N i s k = if i = k then 1 else 0
  assoc : ∀ i j k l,
    Set.Finite {m | N i j m * N m k l ≠ 0} ∧
    Set.Finite {m | N j k m * N i m l ≠ 0} ∧
    ∑ᶠ m, N i j m * N m k l = ∑ᶠ m, N j k m * N i m l

