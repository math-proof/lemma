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
import Structure.v1.Atlas.TensorCategories.code.ModuleFunctorDefs
set_option maxHeartbeats 400000

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

attribute [reassoc] ModuleFunctorHom.compat

namespace ModuleFunctorHom

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
  {N : Type u₃} [Category.{v₃} N] [LeftModuleCategory C N]

/-- Two module functor homs are equal whenever their underlying natural transformations are
equal. -/
@[ext]
theorem ext {F G : ModuleFunctor C M N} {η θ : ModuleFunctorHom F G}
    (h : η.natTrans = θ.natTrans) : η = θ := by
  cases η; cases θ; congr

end ModuleFunctorHom
end CategoryTheory
