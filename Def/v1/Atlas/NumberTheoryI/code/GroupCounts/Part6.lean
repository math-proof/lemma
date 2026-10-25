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
import Theorem.v1.Atlas.NumberTheoryI.code.GroupCounts.Part5
open scoped Classical


namespace GroupCounts

section Z4Z3

noncomputable def subgroupToFinset₄₃ (H : Subgroup G₄₃) : Finset G₄₃ :=
  Finset.univ.filter (· ∈ H)

def kerFinsetMul (a b c : ZMod 4) : Finset G₄₃ :=
  Finset.univ.filter (fun g =>
    a * (Multiplicative.toAdd g).1 + b * (Multiplicative.toAdd g).2.1 +
    c * (Multiplicative.toAdd g).2.2 = 0)

def surjKernelsMul : Finset (Finset G₄₃) :=
  ((Finset.univ : Finset (ZMod 4 × ZMod 4 × ZMod 4)).filter
    (fun abc => decide (isSurjTriple abc.1 abc.2.1 abc.2.2))).image
    (fun abc => kerFinsetMul abc.1 abc.2.1 abc.2.2)

end Z4Z3
end GroupCounts
