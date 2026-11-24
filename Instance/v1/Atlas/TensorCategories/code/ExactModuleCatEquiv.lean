module
public import Def.v1.Atlas.TensorCategories.code.AlgebrasInCategories.Part4
public import Theorem.Category.Atlas.v1.TensorCategories.code.AlgebrasInCategories
public import Theorem.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
public import Theorem.Category.Atlas.v1.TensorCategories.code.InternalHom
public import Theorem.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
public import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
public import Def.v1.Atlas.TensorCategories.code.InternalHom.Part4
public import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Def.v1.Atlas.TensorCategories.code.ExactModuleCatEquiv
set_option maxHeartbeats 800000
set_option autoImplicit false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCatEquiv.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory MonObj LeftModCat

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]


attribute [instance] InternalEndAlgebra.monObj

/-- The default internal algebra is the trivial one on `𝟙_ C`. -/
instance : Inhabited (InternalEndAlgebra (C := C)) where
  default := InternalEndAlgebra.ofUnit


end CategoryTheory
