/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part4
public section

set_option maxHeartbeats 800000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory

open LeftModCat


attribute [reassoc] ModuleNatTrans.compatibility

/-- An equivalence of left `C`-module categories: a `ModuleFunctor` whose underlying functor
is an equivalence of categories. -/
structure ModuleEquivalence
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M₁ : Type u₂) [Category.{v₂} M₁] [LeftModuleCategory C M₁]
    (M₂ : Type u₃) [Category.{v₃} M₂] [LeftModuleCategory C M₂] extends
    ModuleFunctor C M₁ M₂ where
  isEquivalence : toFunctor.IsEquivalence

end CategoryTheory
