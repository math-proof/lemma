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
import Def.v1.Atlas.TensorCategories.code.ZPlusModules
set_option maxHeartbeats 800000

variable {ι : Type*} [DecidableEq ι] [Fintype ι]


/-- A `ℤ_+`-module over a `ℤ_+`-ring `R`: a finite basis set `κ` together with
nonnegative integer action constants `act i l k`, satisfying unitality from `R.I₀`
and a compatibility expressing associativity of the action. -/
structure ZPlusModule (R : ZPlusRing ι) (κ : Type*) [DecidableEq κ] [Fintype κ] where
  act : ι → κ → κ → ℕ
  act_unit : ∀ l k, ∑ s ∈ R.I₀, act s l k = if l = k then 1 else 0
  act_compat : ∀ i j l k,
    ∑ m : ι, R.N i j m * act m l k = ∑ n : κ, act j l n * act i n k

