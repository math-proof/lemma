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
public import Def.v1.Atlas.NumberTheoryI.code.GroupCounts.Part2
open scoped Classical

public section

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
