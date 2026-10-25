/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/AlgebrasInCategoriesDefs.lean -/

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
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Def.v1.Atlas.TensorCategories.code.InternalHom.Part4
import Mathlib.CategoryTheory.Monoidal.Bimod
import Mathlib.CategoryTheory.Monoidal.Mod_
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Abbrev.v1.Atlas.TensorCategories.code.AlgebrasInCategoriesDefs.Part3
set_option maxHeartbeats 400000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj LeftModCat

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable [Limits.HasCoequalizers C]

variable {A : C} [MonObj A]

section FreeModule

variable {A : C} [MonObj A]

/-- Right `A`-module structure on `X ⊗ A` obtained by tensoring on the left by `X` with the
right regular `A`-module. -/
def freeRightModuleObj (X : C) : RightModObj A (X ⊗ A) :=
  RightMod_.tensorModObj X (RightMod_.regular A)

/-- The free right `A`-module on an object `X : C`, namely `X ⊗ A` with the action coming
from multiplication on the right factor. -/
def FreeRightModule (X : C) : RightMod_ (A := A) where
  X := X ⊗ A
  mod := freeRightModuleObj X

end FreeModule

section InternalEnd

open ModuleInternalHom

variable {C₀ : Type*} [Category C₀] [MonoidalCategory C₀]
    {M₀ : Type*} [Category M₀] [LeftModuleCategory C₀ M₀]
    [HasModuleInternalHom C₀ M₀]

/-- The identity morphism `𝟙_ C₀ → Hom̲(m, m)`, obtained from the left unitor `actℓ_ m`
via the defining adjunction of the internal Hom. -/
def moduleIHomId (m : M₀) : 𝟙_ C₀ ⟶ moduleIHom (C := C₀) m m :=
  moduleIHomEquiv (𝟙_ C₀) m m (actℓ_ m).hom

end InternalEnd
end CategoryTheory
