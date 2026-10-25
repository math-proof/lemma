/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Abbrev.v1.Atlas.TensorCategories.code.IndecomposableModuleCat
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_
import Def.v1.Atlas.TensorCategories.code.DualCategory.Part6
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

variable (M : Type u) [Category.{v} M] [LeftModuleCategory C M]

namespace DualCatObj

variable {C M}

attribute [reassoc] Hom.comm

/-- Monoidal category structure data on `DualCatObj C M`: tensor product is functor
composition, the unit is the identity module endofunctor, and the coherence
isomorphisms are the canonical ones. -/
instance dualMonoidalCategoryStruct : MonoidalCategoryStruct (DualCatObj C M) where
  tensorObj := compModuleFunctor
  whiskerLeft := dualWhiskerLeft
  whiskerRight := fun f G => dualWhiskerRight f G
  tensorUnit := idModuleFunctor
  associator := dualAssociator
  leftUnitor := dualLeftUnitor
  rightUnitor := dualRightUnitor


end DualCatObj
end CategoryTheory
