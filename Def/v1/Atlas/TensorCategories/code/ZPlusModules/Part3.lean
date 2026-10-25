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
import Abbrev.v1.Atlas.TensorCategories.code.ZPlusModules.Part3
set_option maxHeartbeats 800000

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {R : ZPlusRing ι} {κ : Type*} [DecidableEq κ] [Fintype κ]


namespace ZPlusModule

variable (M : ZPlusModule R κ)

/-- The sum `∑_{k} act(i, l, k)` of action coefficients of `i ∈ ι` acting on `l ∈ κ`. -/
def actCoeffSum (i : ι) (l : κ) : ℕ := ∑ k : κ, M.act i l k

/-- The total action coefficient at `l ∈ κ`: the sum over all `i ∈ ι` of `actCoeffSum i l`. -/
def totalActCoeff (l : κ) : ℕ := ∑ i : ι, M.actCoeffSum i l

/-- The regular `ℤ_+`-module of a `ℤ_+`-ring `R`: `R` acting on its own basis `ι`
via the structure constants `N`. -/
def regularModule (R : ZPlusRing ι) : ZPlusModule R ι where
  act := R.N
  act_unit := R.unit_mul
  act_compat := R.assoc

end ZPlusModule
