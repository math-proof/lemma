/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleFunctorDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.ExactModuleCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

set_option maxHeartbeats 400000

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Category MonoidalCategory LeftModCat

/-- Alias for `ModuleFunctor` matching the textbook numbering of Definition 2.1.2 (the
notion of a module functor between left `C`-module categories) in EGNO. -/
abbrev Definition_2_1_2_ModuleFunctor
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M]
    (N : Type u₃) [Category.{v₃} N] [LeftModuleCategory C N] :=
  ModuleFunctor C M N

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

attribute [instance] FiniteMultitensorBase.unit_projective
attribute [instance] ExactModuleInfra.abelian ExactModuleInfra.actionRightExact
  ExactModuleInfra.biexact
