module
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Theorem.v1.Atlas.NumberTheoryI.code.GroupCounts.Part6
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

noncomputable def surjTripleOf (s : Finset G₄₃) (hs : s ∈ surjKernelsMul) :
    { abc : ZMod 4 × ZMod 4 × ZMod 4 // isSurjTriple abc.1 abc.2.1 abc.2.2 ∧
      s = kerFinsetMul abc.1 abc.2.1 abc.2.2 } := by
  have : ∃ abc : ZMod 4 × ZMod 4 × ZMod 4, isSurjTriple abc.1 abc.2.1 abc.2.2 ∧
      s = kerFinsetMul abc.1 abc.2.1 abc.2.2 := by
    simp only [surjKernelsMul, Finset.mem_image, Finset.mem_filter] at hs
    obtain ⟨⟨a, b, c⟩, ⟨_, hsurj⟩, heq⟩ := hs
    exact ⟨(a, b, c), of_decide_eq_true hsurj, heq.symm⟩
  exact Classical.indefiniteDescription _ this

end Z4Z3
end GroupCounts
