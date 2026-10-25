/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

/-- A left module category `M` over `C` has internal Hom if for every pair `m, n ∈ M`
there is an object `moduleIHom m n ∈ C` and a natural equivalence
`(X ⊗ᵐ m ⟶ n) ≃ (X ⟶ moduleIHom m n)` (Definition 2.10.2). -/
class HasModuleInternalHom (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M] where
  moduleIHom : M → M → C
  moduleIHomEquiv : ∀ (X : C) (m n : M),
    (X ⊗ᵐ m ⟶ n) ≃ (X ⟶ moduleIHom m n)
  moduleIHomEquiv_natural : ∀ {X Y : C} (f : X ⟶ Y) (m n : M) (g : Y ⊗ᵐ m ⟶ n),
    moduleIHomEquiv X m n (f ▷ᵐ m ≫ g) = f ≫ moduleIHomEquiv Y m n g

end CategoryTheory
