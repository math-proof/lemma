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
public import Theorem.v1.Atlas.NumberTheoryI.code.GroupCounts.Part2

@[expose] public section

open scoped Classical


namespace GroupCounts

section Z2Z4

noncomputable def subgroupIdx2Equiv :
    {H : Subgroup G₂₄ // H.index = 2} ≃
    {s : Finset G₂₄ // s ∈ subgroupCarriersIdx2} where
  toFun := fun ⟨H, hidx⟩ => ⟨subgroupToFinset₂₄ H, by
    rw [mem_subgroupCarriersIdx2]
    exact ⟨(subgroupToFinset₂₄_is_carrier H).1,
      (subgroupToFinset₂₄_is_carrier H).2, by
      rw [subgroupToFinset₂₄_card, (index_eq_two_iff_card_eq_eight H).mp hidx]⟩⟩
  invFun := fun ⟨s, hs⟩ => by
    rw [mem_subgroupCarriersIdx2] at hs
    exact ⟨finsetToSubgroup₂₄ s hs.1 hs.2.1, by
      rw [index_eq_two_iff_card_eq_eight]
      rw [← subgroupToFinset₂₄_card]
      rw [round_trip_finset₂₄]; exact hs.2.2⟩
  left_inv := fun ⟨H, hidx⟩ => by
    simp only; congr 1; exact round_trip_subgroup₂₄ H
  right_inv := fun ⟨s, hs⟩ => by
    simp only; congr 1
    rw [mem_subgroupCarriersIdx2] at hs
    exact round_trip_finset₂₄ s hs.1 hs.2.1

end Z2Z4
end GroupCounts
