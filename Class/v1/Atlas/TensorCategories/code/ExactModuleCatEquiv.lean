/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCatEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.AlgebrasInCategories.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.AlgebrasInCategories
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.InternalHom
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Def.v1.Atlas.TensorCategories.code.InternalHom.Part4
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Instance.v1.Atlas.TensorCategories.code.ExactModuleCatEquiv
set_option maxHeartbeats 800000

set_option autoImplicit false

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory MonObj LeftModCat

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]


attribute [instance] InternalEndAlgebra.monObj

/-- The data needed to set up the internal-Hom functor to right modules over an
internal algebra: a chosen generator `gen ∈ M`, the internal end algebra of `gen`, and
a functor `F` from `M` to right modules over that algebra. -/
class InternalHomData
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [LeftModuleCategory C M] where
  gen : M
  endAlgebra : InternalEndAlgebra (C := C)
  F : M ⥤ RightMod_ (A := endAlgebra.carrier)


variable {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]

/-- The biexactness property of the internal Hom bifunctor on an exact module category:
it preserves monos and epis on the right, and exchanges monos and epis on the left. -/
class InternalHomBiexact
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [ExactModuleCategory C M]
    [HasModuleInternalHom C M] : Prop where
  right_preserves_mono : ∀ (m₁ : M) {m₂ m₂' : M} (f : m₂ ⟶ m₂'),
    Mono f → Mono (moduleIHomMapRight (C := C) m₁ f)
  right_preserves_epi : ∀ (m₁ : M) {m₂ m₂' : M} (f : m₂ ⟶ m₂'),
    Epi f → Epi (moduleIHomMapRight (C := C) m₁ f)
  left_sends_mono_to_epi : ∀ {m₁ m₁' : M} (f : m₁ ⟶ m₁') (m₂ : M),
    Mono f → Epi (moduleIHomMapLeft (C := C) f m₂)
  left_sends_epi_to_mono : ∀ {m₁ m₁' : M} (f : m₁ ⟶ m₁') (m₂ : M),
    Epi f → Mono (moduleIHomMapLeft (C := C) f m₂)

/-- Internal Hom is biexact in any exact module category equipped with internal Homs. -/
class InternalHomExact
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [LeftModuleCategory C M]
    [hom : InternalHomData C M] : Prop where
  preservesEpi : ∀ {N₁ N₂ : M} (f : N₁ ⟶ N₂), Epi f → Epi (hom.F.map f)

/-- The chosen generator `gen` generates the module category: every `N ∈ M` admits an
epimorphism from `X ⊗ gen` for some `X ∈ C`. -/
class InternalHomGeneration
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [LeftModuleCategory C M]
    [hom : InternalHomData C M] : Prop where
  generation : ∀ (N : M), ∃ (X : C) (f : X ⊗ᵐ hom.gen ⟶ N), Epi f


/-- Faithfulness of the internal-Hom functor `F : M ⥤ RightMod (endAlgebra)`. -/
class InternalHomFaithful
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [LeftModuleCategory C M]
    [hom : InternalHomData C M] : Prop where
  faithful : hom.F.Faithful

/-- Fullness of the internal-Hom functor `F : M ⥤ RightMod (endAlgebra)`. -/
class InternalHomFull
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [LeftModuleCategory C M]
    [hom : InternalHomData C M] : Prop where
  full : hom.F.Full

/-- Essential surjectivity of the internal-Hom functor
`F : M ⥤ RightMod (endAlgebra)`. -/
class InternalHomEssSurj
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [LeftModuleCategory C M]
    [hom : InternalHomData C M] : Prop where
  essSurj : hom.F.EssSurj


end CategoryTheory
