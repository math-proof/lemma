/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DeligneTensorProductDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor
set_option maxHeartbeats 400000


noncomputable section

open CategoryTheory

namespace Deligne

section CategoricalFramework

universe w v₁ v₂ v₃ u₁ u₂ u₃

/-- For a fixed object `d : D`, the functor `C ⥤ C × D` sending `c ↦ (c, d)` and
`f ↦ (f, 𝟙 d)`. Used to express right exactness of bifunctors in the first variable. -/
def sliceFunctorRight {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (d : D) : C ⥤ C × D where
  obj c := (c, d)
  map f := (f, 𝟙 d)
  map_id _ := by ext <;> simp
  map_comp _ _ := by ext <;> simp

/-- For a fixed object `c : C`, the functor `D ⥤ C × D` sending `d ↦ (c, d)` and
`g ↦ (𝟙 c, g)`. Used to express right exactness of bifunctors in the second variable. -/
def sliceFunctorLeft {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (c : C) : D ⥤ C × D where
  obj d := (c, d)
  map g := (𝟙 c, g)
  map_id _ := by ext <;> simp
  map_comp _ _ := by ext <;> simp

end CategoricalFramework
end Deligne
end
