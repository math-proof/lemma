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
import Abbrev.v1.Atlas.TensorCategories.code.InternalHom
set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

export HasModuleInternalHom (moduleIHom moduleIHomEquiv moduleIHomEquiv_natural)

/-- Definition 2.10.2: the internal Hom `Hom(m₁, m₂)` in `C` of two module objects of
the module category `M`. -/
def definition_2_10_2 {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    [HasModuleInternalHom C M] (m₁ m₂ : M) : C :=
  moduleIHom (C := C) m₁ m₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    [HasModuleInternalHom C M]

/-- The evaluation morphism `moduleIHom m n ⊗ᵐ m ⟶ n`, obtained as the counit of the
internal Hom adjunction by transporting the identity of `moduleIHom m n`. -/
def moduleIHomEv (m n : M) : (moduleIHom (C := C) m n) ⊗ᵐ m ⟶ n :=
  (moduleIHomEquiv (moduleIHom m n) m n).symm (𝟙 _)

end CategoryTheory
