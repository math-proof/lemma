/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHomFaithfulInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.ExactModuleCatEquiv
import sympy.atlas.v1.Atlas.TensorCategories.code.ConcreteModuleCategories

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

/-- The trivial module functor is faithful: distinct morphisms in `C` yield distinct
morphisms of trivial right `𝟙_ C`-modules. -/
instance trivialModFunctor_faithful : (trivialModFunctor C).Faithful where
  map_injective {N₁ N₂} f g h := by
    have : (trivialRightModHom C f).hom = (trivialRightModHom C g).hom := by
      exact congrArg RightMod_.Hom.hom h
    simpa [trivialRightModHom] using this

/-- The canonical `InternalHomData` for `C` acting on itself: generator `𝟙_ C`,
endomorphism monoid `𝟙_ C`, and the trivial module functor. -/
noncomputable instance selfInternalHomData :
    InternalHomData C C where
  gen := 𝟙_ C
  endAlgebra := ⟨𝟙_ C⟩
  F := trivialModFunctor C

/-- When tensoring preserves projectives, the canonical self internal Hom data is
faithful, via faithfulness of the trivial module functor. -/
instance selfInternalHomFaithful [TensorPreservesProjective C] :
    InternalHomFaithful C C where
  faithful := trivialModFunctor_faithful C

end SelfInternalHomData

end CategoryTheory
