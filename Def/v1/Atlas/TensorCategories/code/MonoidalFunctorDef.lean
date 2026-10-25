/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Structure.v1.Atlas.TensorCategories.code.MonoidalFunctorDef
open CategoryTheory MonoidalCategory

universe v₁ v₂ u₁ u₂


namespace TensorCategories

attribute [instance] def_1_1_2_MonoidalSubcategory.instCat
  def_1_1_2_MonoidalSubcategory.instMonoidal
  def_1_1_2_MonoidalSubcategory.instFaithful

/-- Construct a monoidal subcategory in the sense of EGNO Definition 1.1.2 from any
monoidal `ObjectProperty` on `C`, using the inclusion of the corresponding full
subcategory. -/
def def_1_1_2_MonoidalSubcategory.ofFullSubcategory
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    (P : ObjectProperty C) [P.IsMonoidal] :
    def_1_1_2_MonoidalSubcategory.{v₁, v₁, u₁, u₁} C where
  D := P.FullSubcategory
  ι := P.ι
  instMonoidalFunctor := inferInstance

end TensorCategories
