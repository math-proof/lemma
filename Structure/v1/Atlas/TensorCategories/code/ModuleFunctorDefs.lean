/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleFunctorDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
public import Theorem.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Abbrev.v1.Atlas.TensorCategories.code.ModuleFunctorDefs
public section

set_option maxHeartbeats 400000

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

/-- A morphism of module functors between two left `C`-module categories: a natural
transformation `F.toFunctor ⟶ G.toFunctor` whose components are compatible with the module
structure isomorphisms of `F` and `G`. -/
structure ModuleFunctorHom
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    {N : Type u₃} [Category.{v₃} N] [LeftModuleCategory C N]
    (F G : ModuleFunctor C M N) where
  natTrans : F.toFunctor ⟶ G.toFunctor
  compat : ∀ (X : C) (A : M),
    natTrans.app (X ⊗ᵐ A) ≫ (G.strIso X A).hom =
      (F.strIso X A).hom ≫ X ◁ᵐ (natTrans.app A)

end CategoryTheory
