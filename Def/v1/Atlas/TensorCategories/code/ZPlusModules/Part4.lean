/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ZPlusModules.lean -/

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
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Structure.v1.Atlas.TensorCategories.code.ZPlusModules.Part5
set_option maxHeartbeats 800000

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {R : ZPlusRing ι} {κ : Type*} [DecidableEq κ] [Fintype κ]


namespace ZPlusModule

variable (M : ZPlusModule R κ)

/-- A `ℤ_+`-module is indecomposable if its basis `κ` cannot be split into two
nonempty disjoint action-closed subsets covering `κ`. -/
def IsIndecomposable : Prop :=
  ∀ (S₁ S₂ : Finset κ),
    S₁.Nonempty → S₂.Nonempty → Disjoint S₁ S₂ → S₁ ∪ S₂ = Finset.univ →
    (∀ (i : ι) (l : κ), l ∈ S₁ → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S₁) →
    (∀ (i : ι) (l : κ), l ∈ S₂ → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S₂) →
    False

/-- Exactness of a `ℤ_+`-module: whenever `act i l k ≠ 0` there exists some `j ∈ ι`
with `act j k l ≠ 0`, i.e. the action is symmetric up to relabeling. -/
def IsExact : Prop :=
  ∀ (i : ι) (l k : κ), M.act i l k ≠ 0 → ∃ j : ι, M.act j k l ≠ 0

/-- A subset `S ⊆ κ` is action-closed under `M` if whenever `l ∈ S` and
`M.act i l k ≠ 0` we have `k ∈ S`. -/
def IsActionClosed (S : Finset κ) : Prop :=
  ∀ (i : ι) (l : κ), l ∈ S → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S

/-- An action-closed subset `S ⊆ κ` is an indecomposable piece if it cannot be
partitioned into two nonempty disjoint action-closed subsets. -/
def IsIndecomposablePiece (S : Finset κ) : Prop :=
  ∀ (S₁ S₂ : Finset κ),
    S₁.Nonempty → S₂.Nonempty → Disjoint S₁ S₂ → S₁ ∪ S₂ = S →
    M.IsActionClosed S₁ → M.IsActionClosed S₂ → False

/-- An action-closed subset `S ⊆ κ` is an irreducible piece if it contains no
proper nonempty action-closed subset. -/
def IsIrreduciblePiece (S : Finset κ) : Prop :=
  ∀ T : Finset κ, T.Nonempty → T ≠ S → T ⊆ S → ¬M.IsActionClosed T

end ZPlusModule
