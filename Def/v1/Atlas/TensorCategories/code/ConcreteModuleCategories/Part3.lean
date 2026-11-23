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
public import Theorem.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
public import Theorem.v1.Atlas.TensorCategories.code.DeligneTensorProductMonoidal
public import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Opposite
public import Instance.v1.Atlas.TensorCategories.code.ConcreteModuleCategories.Part2

@[expose] public section

set_option maxHeartbeats 800000

universe v₁ v₂ v₃ vₘ w u₁ u₂ u₃ uₘ


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

section BimoduleCategory

/-- Any multitensor category `C` is a `(C, C)`-bimodule category over itself in the sense of
Definition 2.5.4, with all coherence axioms following from the monoidal pentagon and triangle. -/
noncomputable def selfBimoduleCategory
    (k : Type w) [Field k]
    (C : Type u₁) [Category.{v₁} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] [TensorCategories.MultitensorCategory k C] :
    Definition_2_5_4_BimoduleCategory k C C C where
  __ := selfBimoduleCategoryStruct C
  leftPentagon X Y Z N := by
    simp only [selfBimoduleCategoryStruct]
    exact pentagon X Y Z N
  leftTriangle X N := by
    simp only [selfBimoduleCategoryStruct]
    exact triangle X N
  rightPentagon N X Y Z := by
    simp only [selfBimoduleCategoryStruct]
    exact pentagon N X Y Z
  rightTriangle N Y := by
    simp only [selfBimoduleCategoryStruct]
    exact triangle N Y
  leftMiddlePentagon X Y N Z := by
    simp only [selfBimoduleCategoryStruct]
    exact pentagon X Y N Z
  rightMiddlePentagon X N Y Z := by
    simp only [selfBimoduleCategoryStruct]
    exact pentagon X N Y Z

end BimoduleCategory
end CategoryTheory
