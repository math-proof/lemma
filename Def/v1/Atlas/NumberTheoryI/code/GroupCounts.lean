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
import Abbrev.v1.Atlas.NumberTheoryI.code.GroupCounts
open scoped Classical


namespace GroupCounts

section Z2Z4

noncomputable def subgroupToFinset₂₄ (H : Subgroup G₂₄) : Finset G₂₄ :=
  Finset.univ.filter (· ∈ H)

end Z2Z4
end GroupCounts
