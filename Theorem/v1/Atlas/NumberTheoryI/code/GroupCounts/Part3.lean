/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Def.v1.Atlas.NumberTheoryI.code.GroupCounts.Part3
open scoped Classical


namespace GroupCounts

theorem Z2Z4_index2_count :
    Nat.card {H : Subgroup (Multiplicative (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)) //
      H.index = 2} = 15 := by
  rw [Nat.card_congr subgroupIdx2Equiv, Nat.card_eq_fintype_card,
    Fintype.card_coe, subgroupCarriersIdx2_card]

end GroupCounts
