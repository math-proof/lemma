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
public import Def.v1.Atlas.TensorCategories.code.DualCategory.Part5
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

/-- Composing on the right with the identity module endofunctor does not change the
structure isomorphism. -/
lemma compModuleFunctor_right_id_strIso (F : DualCatObj C M) (X : C) (N : M) :
    (compModuleFunctor F idModuleFunctor).strIso X N = F.strIso X N := by
  ext
  simp [compModuleFunctor, idModuleFunctor, Iso.trans_hom, Functor.mapIso_hom, Iso.refl]

end DualCatObj
end CategoryTheory
