/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCatEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.AlgebrasInCategories.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.AlgebrasInCategories
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.InternalHom
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Def.v1.Atlas.TensorCategories.code.InternalHom.Part4
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
set_option maxHeartbeats 800000

set_option autoImplicit false

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory MonObj LeftModCat

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]


/-- An algebra in `C` represented as a structure carrying both the underlying object
and the `MonObj` instance providing its algebra structure. -/
structure InternalEndAlgebra where
  carrier : C
  [monObj : MonObj carrier]

end CategoryTheory
