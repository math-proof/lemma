/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DirectSumModuleCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Mathlib.CategoryTheory.Products.Basic
import Instance.v1.Atlas.TensorCategories.code.DirectSumModuleCategory
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

section DirectSum

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]

variable (M₁ : Type u₂) [Category.{v₂} M₁] [LeftModuleCategory C M₁]

variable (M₂ : Type u₃) [Category.{v₃} M₂] [LeftModuleCategory C M₂]

/-- Proposition 2.4.1: the direct sum `M = M₁ ⊕ M₂` of two `C`-module categories is
itself a `C`-module category, with componentwise action, associator and unitor. -/
def proposition_2_4_1 : LeftModuleCategory C (M₁ × M₂) :=
  directSumLeftModuleCategory C M₁ M₂

end DirectSum

/-- A `C`-module category `M` is the direct sum of `M₁` and `M₂` (in the sense of
Definition 2.4.2) when `M` is equivalent as a `C`-module category to the product
`M₁ × M₂` equipped with the componentwise action. -/
def IsDirectSumModuleCategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M]
    (M₁ : Type u₃) [Category.{v₃} M₁] [LeftModuleCategory C M₁]
    (M₂ : Type u₄) [Category.{v₄} M₂] [LeftModuleCategory C M₂] : Prop :=
  Nonempty (ModuleEquivalence C M (M₁ × M₂))

end CategoryTheory
