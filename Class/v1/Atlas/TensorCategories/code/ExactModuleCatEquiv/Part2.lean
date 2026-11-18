module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCatEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Def.v1.Atlas.TensorCategories.code.AlgebrasInCategories.Part4
public import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
public import Def.v1.Atlas.TensorCategories.code.InternalHom.Part4
public import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Def.v1.Atlas.TensorCategories.code.ExactModuleCatEquiv.Part2
public section
set_option maxHeartbeats 800000

set_option autoImplicit false

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory MonObj LeftModCat

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

attribute [instance] InternalEndAlgebra.monObj

variable {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]

/-- The internal end algebra produced by the `InternalHomData` package. -/
class ExactModCatInternalHom
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [ExactModuleCategory C M] extends
    InternalHomData C M,
    InternalHomExact C M,
    InternalHomGeneration C M

/-- Theorem (EGNO, Section 2.11): An exact module category equipped with an internal
end algebra and the relevant exactness/generation conditions is equivalent to right
modules over that algebra. -/
class IsIndecomposableModuleCategoryBasic
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M] : Prop where
  nonempty : Nonempty M
  indecomposable : True

/-- Specialization of `exact_module_cat_equiv` to the indecomposable case. -/
class HasProjectiveGenerator
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    [ExactModuleCategory C M] extends
    ExactModCatInternalHom C M

end CategoryTheory
