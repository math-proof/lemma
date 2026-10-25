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
import Instance.v1.Atlas.TensorCategories.code.ModuleFunctorDefs
set_option maxHeartbeats 400000

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

attribute [reassoc] ModuleFunctorHom.compat

/-- A module functor is exact if its underlying functor preserves both monomorphisms and
epimorphisms. -/
class ModuleFunctorIsExact
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    {N : Type u₃} [Category.{v₃} N] [LeftModuleCategory C N]
    (F : ModuleFunctor C M N) : Prop where
  preserves_mono : ∀ {A B : M} (f : A ⟶ B), Mono f → Mono (F.toFunctor.map f)
  preserves_epi : ∀ {A B : M} (f : A ⟶ B), Epi f → Epi (F.toFunctor.map f)

/-- Baseline assumption for a finite multitensor category: the monoidal unit `𝟙_ C` is
projective. -/
class FiniteMultitensorBase (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] : Prop where
  unit_projective : Projective (𝟙_ C)

/-- Bundle of the standard exactness infrastructure on a module category `M`: abelianness,
right-exactness of the action, and biexactness of the action bifunctor. -/
class ExactModuleInfra (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [ExactModuleCategory C M] where
  abelian : Abelian M
  actionRightExact : ExactModuleCategory.ActionRightExact C M
  biexact : ExactModuleCategory.BiexactAction C M

end CategoryTheory
