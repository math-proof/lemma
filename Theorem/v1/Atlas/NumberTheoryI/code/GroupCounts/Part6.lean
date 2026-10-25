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
import Def.v1.Atlas.NumberTheoryI.code.GroupCounts.Part6
open scoped Classical


namespace GroupCounts

section Z4Z3

theorem surjKernelsMul_card : surjKernelsMul.card = 28 := by
  native_decide

lemma ker_carrier_eq_kerFinsetMul (a b c : ZMod 4) :
    subgroupToFinset₄₃ (mulHomTriple a b c).ker = kerFinsetMul a b c := by
  ext g
  rw [subgroupToFinset₄₃_mem, mem_ker_mulHomTriple]
  simp [kerFinsetMul, Finset.mem_filter]

lemma ker_carrier_mem_surjKernels (a b c : ZMod 4) (h : isSurjTriple a b c) :
    subgroupToFinset₄₃ (mulHomTriple a b c).ker ∈ surjKernelsMul := by
  rw [ker_carrier_eq_kerFinsetMul]
  unfold surjKernelsMul
  rw [Finset.mem_image]
  exact ⟨(a, b, c), by simp [Finset.mem_filter, h], rfl⟩

end Z4Z3
end GroupCounts
