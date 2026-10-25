/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHomFaithfulInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.ExactModuleCatEquiv.Part3
import Class.v1.Atlas.TensorCategories.code.ConcreteModuleCategories.Part4
import Def.v1.Atlas.TensorCategories.code.InternalHomFaithfulInstance
set_option autoImplicit false

universe v₁ u₁


namespace CategoryTheory

open Category MonoidalCategory MonObj LeftModCat

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]

section SelfInternalHomData

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
