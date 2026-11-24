module
public import Def.v1.Atlas.TensorCategories.code.AlgebrasInCategories.Part4
public import Theorem.Category.Atlas.v1.TensorCategories.code.AlgebrasInCategories
public import Theorem.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
public import Theorem.Category.Atlas.v1.TensorCategories.code.InternalHom
public import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
public import Def.v1.Atlas.TensorCategories.code.InternalHom.Part4
public import Mathlib.CategoryTheory.Monoidal.Bimod
public import Mathlib.CategoryTheory.Monoidal.Mod_
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Abbrev.v1.Atlas.TensorCategories.code.AlgebrasInCategoriesDefs
set_option maxHeartbeats 400000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/AlgebrasInCategoriesDefs.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj LeftModCat

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An algebra `A` in `C` is exact when the category `RightMod_ A` of right `A`-modules,
viewed as a left `C`-module category, is an exact module category. -/
def IsExactAlgebra (A : C) [MonObj A]
    [LeftModuleCategory C (RightMod_ (A := A))] : Prop :=
  Nonempty (ExactModuleCategory C (RightMod_ (C := C) (A := A)))

end CategoryTheory
