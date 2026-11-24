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
public import Instance.v1.Atlas.TensorCategories.code.DualCategory.Part3
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe v u


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

variable (M : Type u) [Category.{v} M] [LeftModuleCategory C M]

namespace DualCatObj

variable {C M}

attribute [reassoc] Hom.comm

/-- Evaluation of a module endofunctor `F ∈ DualCatObj C M` at an object `N ∈ M`. -/
def evalObj (F : DualCatObj C M) (N : M) : M := F.toFunctor.obj N

/-- Evaluation of a module endofunctor `F` on a morphism of `M`. -/
def evalMap (F : DualCatObj C M) {N₁ N₂ : M} (f : N₁ ⟶ N₂) :
    evalObj F N₁ ⟶ evalObj F N₂ :=
  F.toFunctor.map f

/-- Evaluation of a morphism `α : F₁ ⟶ F₂` of `DualCatObj C M` at an object `N ∈ M`. -/
def evalNatApp {F₁ F₂ : DualCatObj C M} (α : F₁ ⟶ F₂) (N : M) :
    evalObj F₁ N ⟶ evalObj F₂ N :=
  α.natTrans.app N

end DualCatObj
end CategoryTheory
