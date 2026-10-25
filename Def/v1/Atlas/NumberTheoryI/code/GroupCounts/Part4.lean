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
import Abbrev.v1.Atlas.NumberTheoryI.code.GroupCounts.Part2
open scoped Classical


namespace GroupCounts

section Z4Z3

def addHomTriple (a b c : ZMod 4) :
    (ZMod 4 × ZMod 4 × ZMod 4) →+ ZMod 4 where
  toFun := fun ⟨x, y, z⟩ => a * x + b * y + c * z
  map_zero' := by simp
  map_add' := by intro ⟨x₁, y₁, z₁⟩ ⟨x₂, y₂, z₂⟩; simp; ring

def mulHomTriple (a b c : ZMod 4) :
    G₄₃ →* Multiplicative (ZMod 4) :=
  AddMonoidHom.toMultiplicative (addHomTriple a b c)

end Z4Z3
end GroupCounts
