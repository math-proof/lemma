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
import Def.v1.Atlas.NumberTheoryI.code.GroupCounts.Part2
open scoped Classical


namespace GroupCounts

section Z2Z4

theorem subgroupCarriersIdx2_card : subgroupCarriersIdx2.card = 15 := by
  native_decide

lemma mem_subgroupCarriersIdx2 (s : Finset G₂₄) :
    s ∈ subgroupCarriersIdx2 ↔
    (1 : G₂₄) ∈ s ∧ (∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) ∧ s.card = 8 := by
  simp [subgroupCarriersIdx2, Finset.mem_filter]

end Z2Z4
end GroupCounts
