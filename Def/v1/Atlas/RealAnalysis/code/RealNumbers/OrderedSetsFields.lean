/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/RealNumbers/OrderedSetsFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Class.v1.Atlas.RealAnalysis.code.RealNumbers.OrderedSetsFields


namespace OrderedSetsFields

/-- **Least Upper Bound (LUB) Property.** A preordered type `α` has the LUB
property if every nonempty subset `E ⊆ α` that is bounded above has a least
upper bound (supremum) in `α`. -/
def HasLUBProperty (α : Type*) [Preorder α] : Prop :=
  ∀ (E : Set α), E.Nonempty → BddAbove E → ∃ x, IsLUB E x

end OrderedSetsFields
