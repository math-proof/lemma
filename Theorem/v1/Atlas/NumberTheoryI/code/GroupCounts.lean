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
import Def.v1.Atlas.NumberTheoryI.code.GroupCounts
open scoped Classical


namespace GroupCounts

section Z2Z4

lemma index_eq_two_iff_card_eq_eight (H : Subgroup G₂₄) :
    H.index = 2 ↔ Nat.card H = 8 := by
  constructor
  · intro h; have := H.index_mul_card; rw [h, natcard_G₂₄] at this; omega
  · intro h; have := H.index_mul_card; rw [h, natcard_G₂₄] at this; omega

end Z2Z4
end GroupCounts
