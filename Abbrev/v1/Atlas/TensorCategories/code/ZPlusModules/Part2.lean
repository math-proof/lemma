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
import Structure.v1.Atlas.TensorCategories.code.ZPlusModules.Part3
set_option maxHeartbeats 800000

variable {ι : Type*} [DecidableEq ι] [Fintype ι]


/-- Alias for Definition 2.8.1 of Etingof–Gelaki–Nikshych–Ostrik: a `ℤ_+`-module
over a `ℤ_+`-ring is what `ZPlusModule` formalizes. -/
abbrev Definition_2_8_1 := @ZPlusModule

