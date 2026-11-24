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

/-- Convenient abbreviation: an algebra structure on an object `A : C` is a `MonObj A`. -/
abbrev AlgebraObj (A : C) := MonObj A

/-- Convenient abbreviation: a left module structure on `M : C` over the algebra `A` is a
`ModObj A M`. -/
abbrev LeftModObj (A : C) [MonObj A] (M : C) := ModObj A M

/-- Two algebras `A` and `B` in `C` are Morita equivalent if the module categories `Mod_C(A)`
and `Mod_C(B)` are module equivalent. -/
abbrev Definition_2_9_18_MoritaEquivalent (A B : C) [MonObj A] [MonObj B] : Prop :=
  MoritaEquivalent A B

end CategoryTheory
