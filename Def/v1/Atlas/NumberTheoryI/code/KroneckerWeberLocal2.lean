module
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Theorem.v1.Atlas.NumberTheoryI.code.GroupCounts.Part8
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.GroupCounts
public import Class.v1.Atlas.NumberTheoryI.code.KroneckerWeberLocal2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KroneckerWeberLocal2.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace KroneckerWeberLocal2

def LiesInCyclotomicExtension (F : Type*) (K : Type*) [Field F] [Field K]
    [Algebra F K] : Prop :=
  ∃ (m : ℕ+), Nonempty (K →ₐ[F] CyclotomicField (m : ℕ) F)

end KroneckerWeberLocal2
end
