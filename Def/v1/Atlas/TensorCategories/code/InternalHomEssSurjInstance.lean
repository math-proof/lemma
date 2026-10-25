/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHomEssSurjInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.ExactModuleCatEquiv.Part3
import Class.v1.Atlas.TensorCategories.code.ConcreteModuleCategories.Part4
set_option autoImplicit false

universe v u


namespace CategoryTheory

namespace InternalHomEssSurjInst

open Category MonoidalCategory MonObj LeftModCat

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- Equip an object `M` of `C` with the canonical structure of a right module over the
unit monoid `𝟙_ C`, with action given by the right unitor `ρ_M`. -/
def unitRightModObj' (M : C) : RightModObj (𝟙_ C) M where
  act := (ρ_ M).hom
  act_unit := by simp
  act_assoc := by
    simp only [MonObj.mul_def, rightUnitor_naturality]
    simp

/-- The functor sending an object `V` of `C` to itself viewed as a right `𝟙_ C`-module
via `unitRightModObj'`, and a morphism to itself. -/
@[simps]
noncomputable def unitInternalHomFunctor' :
    C ⥤ RightMod_ (A := 𝟙_ C) where
  obj V := ⟨V, unitRightModObj' C V⟩
  map {V W} f := {
    hom := f
    comm := by simp [unitRightModObj']
  }

end InternalHomEssSurjInst
end CategoryTheory
