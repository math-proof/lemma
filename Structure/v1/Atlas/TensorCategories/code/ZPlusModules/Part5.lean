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
import Def.v1.Atlas.TensorCategories.code.ZPlusModules.Part3
set_option maxHeartbeats 800000

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {R : ZPlusRing ι} {κ : Type*} [DecidableEq κ] [Fintype κ]


namespace ZPlusModule

variable (M : ZPlusModule R κ)

/-- A morphism of `ℤ_+`-modules over the same `ℤ_+`-ring `R`: a nonnegative integer
matrix `toMatrix : κ₁ → κ₂ → ℕ` that intertwines the two actions of `R`. -/
structure ZPlusModuleHom {κ₁ κ₂ : Type*} [DecidableEq κ₁] [Fintype κ₁]
    [DecidableEq κ₂] [Fintype κ₂]
    (M₁ : ZPlusModule R κ₁) (M₂ : ZPlusModule R κ₂) where
  toMatrix : κ₁ → κ₂ → ℕ
  equivariant : ∀ (i : ι) (l : κ₁) (k₂ : κ₂),
    ∑ k₁ : κ₁, M₁.act i l k₁ * toMatrix k₁ k₂ =
    ∑ n : κ₂, toMatrix l n * M₂.act i n k₂

/-- An isomorphism between two `ℤ_+`-modules: a bijection of basis sets `κ₁ ≃ κ₂`
that intertwines the two actions of `R`. -/
structure IsIsomorphism {κ₁ κ₂ : Type*} [DecidableEq κ₁] [Fintype κ₁]
    [DecidableEq κ₂] [Fintype κ₂]
    (M₁ : ZPlusModule R κ₁) (M₂ : ZPlusModule R κ₂) where
  equiv : κ₁ ≃ κ₂
  compat : ∀ (i : ι) (l k : κ₁), M₁.act i l k = M₂.act i (equiv l) (equiv k)

end ZPlusModule
