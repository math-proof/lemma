/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean -/

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
public import Abbrev.v1.Atlas.TensorCategories.code.IndecomposableModuleCat
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon_
public import Structure.v1.Atlas.TensorCategories.code.DualCategory.Part3
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

public section

universe v u


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

variable (M : Type u) [Category.{v} M] [LeftModuleCategory C M]

attribute [reassoc] DrinfeldCenterHalfBraidingHom.comm

/-- Two half-braiding morphisms are equal whenever their underlying morphisms in `C`
agree. -/
@[ext]
theorem DrinfeldCenterHalfBraidingHom.ext {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {P Q : DrinfeldCenterHalfBraidingObj C} {f g : DrinfeldCenterHalfBraidingHom P Q}
    (h : f.hom = g.hom) : f = g := by
  cases f; cases g; congr

end CategoryTheory
