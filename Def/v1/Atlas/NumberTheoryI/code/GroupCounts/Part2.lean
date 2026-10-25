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
import Theorem.v1.Atlas.NumberTheoryI.code.GroupCounts
open scoped Classical


namespace GroupCounts

section Z2Z4

noncomputable def finsetToSubgroup₂₄ (s : Finset G₂₄)
    (h1 : (1 : G₂₄) ∈ s) (hmul : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) :
    Subgroup G₂₄ where
  carrier := {g | g ∈ s}
  mul_mem' {a b} ha hb := hmul a ha b hb
  one_mem' := h1
  inv_mem' {a} ha := by rw [G₂₄_inv_eq_self]; exact ha

def subgroupCarriersIdx2 : Finset (Finset G₂₄) :=
  (Finset.univ : Finset G₂₄).powerset.filter
    (fun s => decide ((1 : G₂₄) ∈ s ∧
      (∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) ∧ s.card = 8))

end Z2Z4
end GroupCounts
