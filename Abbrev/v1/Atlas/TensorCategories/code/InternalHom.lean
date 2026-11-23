/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
public import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
public import Theorem.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Notation.v1.Atlas.TensorCategories.code.InternalHom
@[expose] public section

set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

export HasModuleInternalHom (moduleIHom moduleIHomEquiv moduleIHomEquiv_natural)

/-- Convenience abbreviation for `moduleIHom m₁ m₂`, the internal Hom in `C` of the
module objects `m₁, m₂ : M`. -/
abbrev internalModuleHom {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    [HasModuleInternalHom C M] (m₁ m₂ : M) : C :=
  moduleIHom (C := C) m₁ m₂

end CategoryTheory
