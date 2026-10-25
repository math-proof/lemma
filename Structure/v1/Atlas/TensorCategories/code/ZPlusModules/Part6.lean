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
import Def.v1.Atlas.TensorCategories.code.ZPlusModules.Part4
set_option maxHeartbeats 800000

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {R : ZPlusRing ι} {κ : Type*} [DecidableEq κ] [Fintype κ]


namespace ZPlusModule

variable (M : ZPlusModule R κ)

/-- A `ℤ_+`-decomposition of `M`: a finite family of nonempty pairwise disjoint
action-closed subsets of `κ` whose union covers `κ`. -/
structure IsZPlusDecomposition (parts : Finset (Finset κ)) : Prop where
  covers : ∀ k : κ, ∃ P ∈ parts, k ∈ P
  pairwise_disjoint : ∀ P₁ ∈ parts, ∀ P₂ ∈ parts, P₁ ≠ P₂ → Disjoint P₁ P₂
  nonempty : ∀ P ∈ parts, P.Nonempty
  closed : ∀ P ∈ parts, M.IsActionClosed P

end ZPlusModule
