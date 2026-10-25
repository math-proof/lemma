/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/AlgebrasInCategories.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Instance.v1.Atlas.TensorCategories.code.AlgebrasInCategories
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable (A : C) [MonObj A]

attribute [reassoc (attr := simp)] RightModObj.act_unit RightModObj.act_assoc

variable {A}

attribute [reassoc (attr := simp)] RightMod_.Hom.comm

namespace RightMod_

/-- Two morphisms of right `A`-modules are equal iff their underlying morphisms in `C`
are equal. -/
@[ext]
lemma hom_ext {M N : RightMod_ A} (f₁ f₂ : M ⟶ N) (h : f₁.hom = f₂.hom) : f₁ = f₂ :=
  Hom.ext h

/-- The underlying morphism of the identity in `RightMod_ A` is the identity in `C`. -/
@[simp] lemma id_hom' (M : RightMod_ A) : (𝟙 M : M ⟶ M).hom = 𝟙 M.X := rfl

/-- The underlying morphism of a composition `f ≫ g` of right `A`-module morphisms is the
composition of the underlying morphisms. -/
@[simp] lemma comp_hom' {M N K : RightMod_ A} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

end RightMod_
end CategoryTheory
