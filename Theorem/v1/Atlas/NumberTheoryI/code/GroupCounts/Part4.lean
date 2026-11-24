module
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Def.v1.Atlas.NumberTheoryI.code.GroupCounts.Part4
open scoped Classical


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCounts.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
