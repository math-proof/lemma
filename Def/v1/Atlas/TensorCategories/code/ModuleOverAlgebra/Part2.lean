/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleOverAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Mod_
import Mathlib.CategoryTheory.Monoidal.Mon_
import Abbrev.v1.Atlas.TensorCategories.code.ModuleOverAlgebra
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

attribute [reassoc (attr := simp)] Definition_2_9_5.act_assoc Definition_2_9_5.act_unit

attribute [reassoc] AModuleHom.comm

namespace AModuleHom

variable {A : C} [MonObj A] {M₁ M₂ M₃ : C}
  {p₁ : Definition_2_9_5 A M₁} {p₂ : Definition_2_9_5 A M₂}
  {p₃ : Definition_2_9_5 A M₃}

/-- The identity module hom on an `A`-module `(M₁, p)`, given by the identity morphism. -/
@[simps]
def id (p : Definition_2_9_5 A M₁) : AModuleHom p p where
  hom := 𝟙 M₁
  comm := by simp

/-- Composition of module homs: the underlying morphisms are composed and the compatibility
square with the actions is verified. -/
@[simps]
def comp (f : AModuleHom p₁ p₂) (g : AModuleHom p₂ p₃) : AModuleHom p₁ p₃ where
  hom := f.hom ≫ g.hom
  comm := by
    rw [← Category.assoc, f.comm, Category.assoc, g.comm, ← Category.assoc,
        (comp_whiskerRight f.hom g.hom A).symm]

end AModuleHom
end CategoryTheory
