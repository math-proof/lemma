/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHomFaithfulInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.ExactModuleCatEquiv.Part3
import Class.v1.Atlas.TensorCategories.code.ConcreteModuleCategories.Part4
set_option autoImplicit false

universe v₁ u₁


namespace CategoryTheory

open Category MonoidalCategory MonObj LeftModCat

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]

section SelfInternalHomData

/-- The trivial right `𝟙_ C`-module structure on an object `N`, given by the right
unitor as the action. -/
def trivialRightModObj (N : C) : RightModObj (𝟙_ C) N where
  act := (ρ_ N).hom
  act_unit := by simp
  act_assoc := by simp [triangle_assoc]

/-- Bundle `trivialRightModObj` into an object of `RightMod_ (𝟙_ C)`. -/
def trivialRightMod (N : C) : RightMod_ (A := 𝟙_ C) where
  X := N
  mod := trivialRightModObj C N

/-- A morphism `f : N₁ ⟶ N₂` in `C` induces a morphism of trivial right `𝟙_ C`-modules
with the same underlying morphism. -/
def trivialRightModHom {N₁ N₂ : C} (f : N₁ ⟶ N₂) :
    trivialRightMod C N₁ ⟶ trivialRightMod C N₂ where
  hom := f
  comm := by
    simp only [trivialRightMod, trivialRightModObj]
    exact (rightUnitor_naturality f).symm

/-- The functor sending each object of `C` to the corresponding trivial right
`𝟙_ C`-module, and each morphism to itself. -/
@[simps]
noncomputable def trivialModFunctor : C ⥤ RightMod_ (A := 𝟙_ C) where
  obj N := trivialRightMod C N
  map f := trivialRightModHom C f
  map_id N := by
    apply RightMod_.hom_ext
    simp [trivialRightModHom, trivialRightMod]
  map_comp f g := by
    apply RightMod_.hom_ext
    rfl

end SelfInternalHomData
end CategoryTheory
