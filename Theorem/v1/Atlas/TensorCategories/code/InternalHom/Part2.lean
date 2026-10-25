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
import Def.v1.Atlas.TensorCategories.code.InternalHom.Part2
set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

export HasModuleInternalHom (moduleIHom moduleIHomEquiv moduleIHomEquiv_natural)

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    [HasModuleInternalHom C M]

omit [HasModuleInternalHom C M] in
/-- Right whiskering of a composition of morphisms in `C` by a module object equals the
composition of right whiskerings. -/
@[reassoc]
lemma actWhiskerRight_comp {X₁ X₂ X₃ : C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (N : M) :
    (f ≫ g) ▷ᵐ N = f ▷ᵐ N ≫ g ▷ᵐ N := by
  have h := LeftModuleCategory.actTensorHom_comp (M := M) f (𝟙 N) g (𝟙 N)
  simp [LeftModuleCategory.actTensorHom_def] at h; exact h.symm

end CategoryTheory
