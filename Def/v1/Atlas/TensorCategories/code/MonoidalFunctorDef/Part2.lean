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
import Structure.v1.Atlas.TensorCategories.code.MonoidalFunctorDef.Part2
open CategoryTheory MonoidalCategory

universe v₁ v₂ u₁ u₂


namespace TensorCategories

attribute [instance] def_1_1_2_MonoidalSubcategory.instCat
  def_1_1_2_MonoidalSubcategory.instMonoidal
  def_1_1_2_MonoidalSubcategory.instFaithful

section MonoidalFunctor

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
  (D : Type u₂) [Category.{v₂} D] [MonoidalCategory D]

attribute [instance] def_1_4_1_MonoidalFunctor.instMonoidal

/-- The monoidal structure morphism `J : F X ⊗ F Y ≅ F (X ⊗ Y)` of EGNO Definition 1.4.1,
extracted from the underlying `Functor.Monoidal` instance. -/
def def_1_4_1_MonoidalFunctor.J {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    (MF : def_1_4_1_MonoidalFunctor C D) (X Y : C) :
    MF.F.obj X ⊗ MF.F.obj Y ≅ MF.F.obj (X ⊗ Y) :=
  @Functor.Monoidal.μIso _ _ _ _ _ _ MF.F MF.instMonoidal X Y

end MonoidalFunctor
end TensorCategories
