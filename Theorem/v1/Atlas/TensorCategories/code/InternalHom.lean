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
import Def.v1.Atlas.TensorCategories.code.InternalHom
set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

export HasModuleInternalHom (moduleIHom moduleIHomEquiv moduleIHomEquiv_natural)

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    [HasModuleInternalHom C M]

/-- The inverse of `moduleIHomEquiv` is given by whiskering by `m` and post-composing
with the evaluation morphism. -/
theorem moduleIHomEquiv_symm_eq (X : C) (m n : M) (h : X ⟶ moduleIHom (C := C) m n) :
    (moduleIHomEquiv X m n).symm h = h ▷ᵐ m ≫ moduleIHomEv m n := by
  apply (moduleIHomEquiv X m n).injective
  rw [Equiv.apply_symm_apply]
  have key := moduleIHomEquiv_natural h m n (moduleIHomEv m n)
  rw [key]
  simp [moduleIHomEv, Equiv.apply_symm_apply]

end CategoryTheory
