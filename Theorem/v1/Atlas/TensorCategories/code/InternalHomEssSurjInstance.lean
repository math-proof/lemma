/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHomEssSurjInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.ExactModuleCatEquiv.Part3
import Class.v1.Atlas.TensorCategories.code.ConcreteModuleCategories.Part4
import Instance.v1.Atlas.TensorCategories.code.InternalHomEssSurjInstance
set_option autoImplicit false

universe v u


namespace CategoryTheory

namespace InternalHomEssSurjInst

open Category MonoidalCategory MonObj LeftModCat

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- Every right module over the unit monoid `𝟙_ C` has its action map equal to the right
unitor of the underlying object, i.e. `L.mod.act = (ρ_ L.X).hom`. -/
theorem rightMod_unit_act_eq' (L : RightMod_ (A := 𝟙_ C)) :
    L.mod.act = (ρ_ L.X).hom := by
  have h := L.mod.act_unit
  simp at h
  exact h

end InternalHomEssSurjInst
end CategoryTheory
