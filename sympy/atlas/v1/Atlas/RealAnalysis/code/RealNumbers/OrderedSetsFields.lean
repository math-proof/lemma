/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/RealNumbers/OrderedSetsFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace OrderedSetsFields

/-- **Ordered set.** A type `α` equipped with a relation `lt : α → α → Prop` is
an ordered set if it satisfies trichotomy (for any `x y`, exactly one of `lt x y`,
`lt y x`, or `x = y` holds) and transitivity (`lt x y` and `lt y z` imply `lt x z`). -/
class IsOrderedSet (α : Type*) (lt : α → α → Prop) : Prop where
  trichotomy : ∀ x y : α, lt x y ∨ lt y x ∨ x = y
  transitivity : ∀ x y z : α, lt x y → lt y z → lt x z

/-- **Least Upper Bound (LUB) Property.** A preordered type `α` has the LUB
property if every nonempty subset `E ⊆ α` that is bounded above has a least
upper bound (supremum) in `α`. -/
def HasLUBProperty (α : Type*) [Preorder α] : Prop :=
  ∀ (E : Set α), E.Nonempty → BddAbove E → ∃ x, IsLUB E x
