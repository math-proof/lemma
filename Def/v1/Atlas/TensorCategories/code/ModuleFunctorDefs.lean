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
import Theorem.v1.Atlas.TensorCategories.code.ModuleFunctorDefs
set_option maxHeartbeats 400000

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

attribute [reassoc] ModuleFunctorHom.compat

namespace ModuleFunctorHom

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
  {N : Type u₃} [Category.{v₃} N] [LeftModuleCategory C N]

/-- The identity module functor hom on `F`, given by the identity natural transformation. -/
@[simps]
protected def id (F : ModuleFunctor C M N) : ModuleFunctorHom F F where
  natTrans := 𝟙 F.toFunctor
  compat X A := by simp

/-- Composition of module functor homs: the underlying natural transformations are composed
and the compatibility square is verified. -/
@[simps]
protected def comp {F G H : ModuleFunctor C M N}
    (η : ModuleFunctorHom F G) (θ : ModuleFunctorHom G H) :
    ModuleFunctorHom F H where
  natTrans := η.natTrans ≫ θ.natTrans
  compat X A := by
    simp only [NatTrans.comp_app, assoc]
    rw [θ.compat X A, ← assoc, η.compat X A, assoc]
    congr 1


    have := LeftModuleCategory.actTensorHom_comp (𝟙 X) (η.natTrans.app A) (𝟙 X) (θ.natTrans.app A)
    simp [LeftModuleCategory.actTensorHom_def] at this
    exact this

end ModuleFunctorHom
end CategoryTheory
