/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHomEssSurjInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.ExactModuleCatEquiv.Part3
import Class.v1.Atlas.TensorCategories.code.ConcreteModuleCategories.Part4
import Theorem.v1.Atlas.TensorCategories.code.InternalHomEssSurjInstance
set_option autoImplicit false

universe v u


namespace CategoryTheory

namespace InternalHomEssSurjInst

open Category MonoidalCategory MonObj LeftModCat

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- For each right `𝟙_ C`-module `L`, the canonical isomorphism between the image of
`L.X` under `unitInternalHomFunctor'` and `L` itself, with identity underlying morphism. -/
noncomputable def rightModUnitIso' (L : RightMod_ (A := 𝟙_ C)) :
    (unitInternalHomFunctor' C).obj L.X ≅ L where
  hom := {
    hom := 𝟙 L.X
    comm := by
      simp [unitInternalHomFunctor', unitRightModObj']
      exact (rightMod_unit_act_eq' C L).symm
  }
  inv := {
    hom := 𝟙 L.X
    comm := by
      simp [unitInternalHomFunctor', unitRightModObj']
      exact rightMod_unit_act_eq' C L
  }

end InternalHomEssSurjInst
end CategoryTheory
