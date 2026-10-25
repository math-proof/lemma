/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCatDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.TensorCategories.code.ModuleFunctor
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.Logic.UnivLE
import Instance.v1.Atlas.TensorCategories.code.DualCatDefs
set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory ModFun

/-- Category structure on `DualCatObj' C M` whose morphisms are obtained by shrinking
the natural transformations between the underlying module functors. -/
@[reducible]
class HasModuleInternalHom'
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M] where
  moduleIHom' : M → M → C
  moduleIHomEquiv' : ∀ (X : C) (m n : M),
    (X ⊗ᵐ m ⟶ n) ≃ (X ⟶ moduleIHom' m n)
  moduleIHomEquiv'_natural : ∀ {X Y : C} (f : X ⟶ Y) (m n : M) (g : Y ⊗ᵐ m ⟶ n),
    moduleIHomEquiv' X m n (f ▷ᵐ m ≫ g) = f ≫ moduleIHomEquiv' Y m n g

end CategoryTheory
