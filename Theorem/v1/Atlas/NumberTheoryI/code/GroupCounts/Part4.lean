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
import Def.v1.Atlas.NumberTheoryI.code.GroupCounts.Part4
open scoped Classical


namespace GroupCounts

section Z4Z3

lemma mem_ker_mulHomTriple (a b c : ZMod 4) (g : G₄₃) :
    g ∈ (mulHomTriple a b c).ker ↔
    a * g.toAdd.1 + b * g.toAdd.2.1 + c * g.toAdd.2.2 = 0 := by
  simp [MonoidHom.mem_ker, mulHomTriple, AddMonoidHom.toMultiplicative,
        addHomTriple, Multiplicative.ofAdd, Multiplicative.toAdd]
  rfl

end Z4Z3
end GroupCounts
