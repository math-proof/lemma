/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ConcreteModuleCategories.lean -/

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
public import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
public import Theorem.v1.Atlas.TensorCategories.code.DeligneTensorProductMonoidal
public import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Opposite
public import Class.v1.Atlas.TensorCategories.code.ConcreteModuleCategories
public section

set_option maxHeartbeats 800000

universe v₁ v₂ v₃ vₘ w u₁ u₂ u₃ uₘ


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

section BimoduleCategory

/-- Structure of a `(C, D)`-bimodule category on `M`: combines compatible left `C`-action
and right `D`-action data with a middle interchange isomorphism. -/
structure BimoduleCategoryStruct
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (D : Type*) [Category D] [MonoidalCategory D]
    (M : Type*) [Category M] where
  lactObj : C → M → M
  ractObj : M → D → M
  lactWhiskerLeft (X : C) {N₁ N₂ : M} (f : N₁ ⟶ N₂) :
    lactObj X N₁ ⟶ lactObj X N₂
  lactWhiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (N : M) :
    lactObj X₁ N ⟶ lactObj X₂ N
  ractWhiskerLeft {N₁ N₂ : M} (f : N₁ ⟶ N₂) (Y : D) :
    ractObj N₁ Y ⟶ ractObj N₂ Y
  ractWhiskerRight (N : M) {Y₁ Y₂ : D} (f : Y₁ ⟶ Y₂) :
    ractObj N Y₁ ⟶ ractObj N Y₂
  lactAssociator : ∀ (X Y : C) (N : M),
    lactObj (X ⊗ Y) N ≅ lactObj X (lactObj Y N)
  ractAssociator : ∀ (N : M) (X Y : D),
    ractObj (ractObj N X) Y ≅ ractObj N (X ⊗ Y)
  lactLeftUnitor : ∀ (N : M), lactObj (𝟙_ C) N ≅ N
  ractRightUnitor : ∀ (N : M), ractObj N (𝟙_ D) ≅ N
  middleInterchange : ∀ (X : C) (N : M) (Y : D),
    ractObj (lactObj X N) Y ≅ lactObj X (ractObj N Y)

end BimoduleCategory
end CategoryTheory
