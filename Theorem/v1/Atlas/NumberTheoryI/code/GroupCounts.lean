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
public import Def.v1.Atlas.NumberTheoryI.code.GroupCounts
open scoped Classical

public section

namespace GroupCounts

section Z2Z4

lemma index_eq_two_iff_card_eq_eight (H : Subgroup G₂₄) :
    H.index = 2 ↔ Nat.card H = 8 := by
  constructor
  · intro h; have := H.index_mul_card; rw [h, natcard_G₂₄] at this; omega
  · intro h; have := H.index_mul_card; rw [h, natcard_G₂₄] at this; omega

end Z2Z4
end GroupCounts
