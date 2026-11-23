/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/AlgebrasInCategoriesDefsBatch.lean -/

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
public import Mathlib.CategoryTheory.Monoidal.Bimod
public import Mathlib.CategoryTheory.Monoidal.Mod_
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Abbrev.v1.Atlas.TensorCategories.code.AlgebrasInCategoriesDefsBatch

@[expose] public section

set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Two algebras `A` and `B` in `C` are Morita equivalent if the module categories `Mod_C(A)`
and `Mod_C(B)` are module equivalent. Stated here directly for module categories `M₁` and `M₂`
as the existence of a module equivalence between them. -/
def Definition_2_9_18_MoritaEquivalence
    (M₁ : Type*) (M₂ : Type*)
    [Category M₁] [Category M₂]
    [LeftModuleCategory C M₁]
    [LeftModuleCategory C M₂] : Prop :=
  Nonempty (ModuleEquivalence C M₁ M₂)

/-- An algebra `A` in the category `C` is exact if the module category `Mod_C(A)` is exact. -/
def Definition_2_9_21_ExactAlgebra
    (A : C) [MonObj A]
    [LeftModuleCategory C (Mod_ C A)] : Prop :=
  Nonempty (ExactModuleCategory C (Mod_ C A))

end CategoryTheory
