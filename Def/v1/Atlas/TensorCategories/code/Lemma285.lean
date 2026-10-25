/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Lemma285.lean -/

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
import Structure.v1.Atlas.TensorCategories.code.Lemma285
set_option maxHeartbeats 800000

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {R : ZPlusRing' ι} {κ : Type*} [DecidableEq κ] [Fintype κ]


namespace ZPlusModule'

variable (M : ZPlusModule' R κ)

/-- `M` is irreducible (primed variant) if it has no nontrivial `ℤ₊`-submodule. -/
def IsIrreducible' : Prop := ∀ S : Finset κ, ¬M.IsZPlusSubmodule' S

/-- `M` is indecomposable (primed variant) if there is no partition of its basis into two
nonempty disjoint subsets, each closed under the action. -/
def IsIndecomposable' : Prop :=
  ∀ (S₁ S₂ : Finset κ),
    S₁.Nonempty → S₂.Nonempty → Disjoint S₁ S₂ → S₁ ∪ S₂ = Finset.univ →
    (∀ (i : ι) (l : κ), l ∈ S₁ → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S₁) →
    (∀ (i : ι) (l : κ), l ∈ S₂ → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S₂) →
    False

/-- `M` is exact (primed variant) if whenever `act i l k ≠ 0` there is some `j` such that
`act j k l ≠ 0`; this is the combinatorial analogue of exactness from EGNO. -/
def IsExact' : Prop :=
  ∀ (i : ι) (l k : κ), M.act i l k ≠ 0 → ∃ j : ι, M.act j k l ≠ 0

end ZPlusModule'
