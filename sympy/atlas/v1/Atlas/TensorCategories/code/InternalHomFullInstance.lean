/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHomFullInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.InternalHomFaithfulInstance

set_option autoImplicit false

universe v₁ u₁

namespace CategoryTheory

open Category MonoidalCategory MonObj LeftModCat

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]

section SelfInternalHomFull

/-- The trivial module functor `C ⥤ RightMod_ (𝟙_ C)` is full: every morphism of right
`𝟙_ C`-modules between trivial modules comes from a morphism in `C`. -/
instance trivialModFunctor_full : (trivialModFunctor C).Full where
  map_surjective φ := ⟨φ.hom, RightMod_.hom_ext _ _ rfl⟩

/-- When tensoring preserves projectives, the canonical self internal Hom data is full,
inherited from fullness of the trivial module functor. -/
instance selfInternalHomFull [TensorPreservesProjective C] :
    InternalHomFull C C where
  full := trivialModFunctor_full C

end SelfInternalHomFull

end CategoryTheory
