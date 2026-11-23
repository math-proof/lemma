/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Def.v1.Atlas.NumberTheoryI.code.GroupCounts.Part3
open scoped Classical

public section

namespace GroupCounts

theorem Z2Z4_index2_count :
    Nat.card {H : Subgroup (Multiplicative (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)) //
      H.index = 2} = 15 := by
  rw [Nat.card_congr subgroupIdx2Equiv, Nat.card_eq_fintype_card,
    Fintype.card_coe, subgroupCarriersIdx2_card]

end GroupCounts
