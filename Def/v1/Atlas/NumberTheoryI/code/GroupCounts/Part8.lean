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
import Theorem.v1.Atlas.NumberTheoryI.code.GroupCounts.Part7
open scoped Classical


namespace GroupCounts

section Z4Z3

noncomputable def subgroupCyclicIdx4Equiv :
    {H : Subgroup G₄₃ // H.index = 4 ∧
      IsCyclic (G₄₃ ⧸ H)} ≃
    {s : Finset G₄₃ // s ∈ surjKernelsMul} where
  toFun := fun ⟨H, hidx, hcyc⟩ =>
    ⟨subgroupToFinset₄₃ H, carrier_of_cyclic_idx4_in_surjKernels H hidx hcyc⟩
  invFun := fun ⟨s, hs⟩ =>
    let t := surjTripleOf s hs
    ⟨(mulHomTriple t.1.1 t.1.2.1 t.1.2.2).ker,
     mulHomTriple_ker_index t.1.1 t.1.2.1 t.1.2.2 t.2.1,
     mulHomTriple_ker_isCyclic t.1.1 t.1.2.1 t.1.2.2 t.2.1⟩
  left_inv := fun ⟨H, hidx, hcyc⟩ => by
    simp only
    have hmem := carrier_of_cyclic_idx4_in_surjKernels H hidx hcyc
    let t := surjTripleOf (subgroupToFinset₄₃ H) hmem
    have heq : subgroupToFinset₄₃ H = kerFinsetMul t.1.1 t.1.2.1 t.1.2.2 := t.2.2
    congr 1
    rw [← ker_carrier_eq_kerFinsetMul] at heq
    exact subgroupToFinset₄₃_injective heq.symm
  right_inv := fun ⟨s, hs⟩ => by
    simp only
    let t := surjTripleOf s hs
    have heq : s = kerFinsetMul t.1.1 t.1.2.1 t.1.2.2 := t.2.2
    congr 1
    rw [ker_carrier_eq_kerFinsetMul]
    exact heq.symm

end Z4Z3
end GroupCounts
