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
import Structure.v1.Atlas.TensorCategories.code.ZPlusModules
set_option maxHeartbeats 800000


/-- Alias for Definition 1.42.1 of Etingof–Gelaki–Nikshych–Ostrik: a `ℤ_+`-ring is the
general (possibly infinite-index) version `ZPlusRingGen`. -/
abbrev Definition_1_42_1 := ZPlusRingGen

