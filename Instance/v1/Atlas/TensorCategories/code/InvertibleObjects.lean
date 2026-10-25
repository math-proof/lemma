/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InvertibleObjects.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Def.v1.Atlas.TensorCategories.code.InvertibleObjects.Part2
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

universe v u


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable [RigidCategory C]

section InvertibleSubcategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- The collection of invertible objects in a rigid monoidal category is closed under
the monoidal unit and tensor product, hence forms a monoidal subcategory. -/
noncomputable instance : (IsInvertibleObjectProp (C := C)).IsMonoidal where
  prop_unit := ⟨unit_invertible⟩
  prop_tensor := fun X Y ⟨hX⟩ ⟨hY⟩ => ⟨tensor_invertible X Y (hX := hX) (hY := hY)⟩

end InvertibleSubcategory
end CategoryTheory
