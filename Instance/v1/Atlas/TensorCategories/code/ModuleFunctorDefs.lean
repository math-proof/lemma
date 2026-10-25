/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleFunctorDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Def.v1.Atlas.TensorCategories.code.ModuleFunctorDefs
set_option maxHeartbeats 400000

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

attribute [reassoc] ModuleFunctorHom.compat

/-- The category structure on `ModuleFunctor C M N` with module functor homs as morphisms,
identity and composition as defined by `ModuleFunctorHom.id` and `ModuleFunctorHom.comp`. -/
instance moduleFunctorCategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M]
    (N : Type u₃) [Category.{v₃} N] [LeftModuleCategory C N] :
    Category (ModuleFunctor C M N) where
  Hom F G := ModuleFunctorHom F G
  id F := ModuleFunctorHom.id F
  comp η θ := ModuleFunctorHom.comp η θ
  id_comp η := by
    apply ModuleFunctorHom.ext
    simp [ModuleFunctorHom.comp, ModuleFunctorHom.id]
  comp_id η := by
    apply ModuleFunctorHom.ext
    simp [ModuleFunctorHom.comp, ModuleFunctorHom.id]
  assoc η θ ξ := by
    apply ModuleFunctorHom.ext
    simp [ModuleFunctorHom.comp]

end CategoryTheory
