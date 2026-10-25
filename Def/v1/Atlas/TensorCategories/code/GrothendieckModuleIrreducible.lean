/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckModuleIrreducible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Structure.v1.Atlas.TensorCategories.code.GrothendieckModuleIrreducible
set_option maxHeartbeats 800000

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {R : ZPlusRingIrr ι} {κ : Type*} [DecidableEq κ] [Fintype κ]


namespace ZPlusModuleIrr

variable (M : ZPlusModuleIrr R κ)

/-- The `ℤ₊`-module `M` is irreducible if it admits no proper `ℤ₊`-submodule. -/
def IsIrreducible : Prop := ∀ S : Finset κ, ¬M.IsZPlusSubmodule S

/-- The `ℤ₊`-module `M` is indecomposable if `κ` cannot be partitioned into two nonempty
disjoint subsets each closed under the action. -/
def IsIndecomposable : Prop :=
  ∀ (S₁ S₂ : Finset κ),
    S₁.Nonempty → S₂.Nonempty → Disjoint S₁ S₂ → S₁ ∪ S₂ = Finset.univ →
    (∀ (i : ι) (l : κ), l ∈ S₁ → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S₁) →
    (∀ (i : ι) (l : κ), l ∈ S₂ → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S₂) →
    False

/-- The `ℤ₊`-module `M` is exact if whenever some basis element of the ring sends `l` to
`k` with nonzero coefficient, there is also a basis element sending `k` back to `l`. -/
def IsExact : Prop :=
  ∀ (i : ι) (l k : κ), M.act i l k ≠ 0 → ∃ j : ι, M.act j k l ≠ 0

end ZPlusModuleIrr
