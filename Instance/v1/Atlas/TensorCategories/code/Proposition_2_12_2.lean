/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_2_12_2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.TensorCategories.code.ModuleFunctorAbelianDefs
import Mathlib.CategoryTheory.Monoidal.Bimod
import Mathlib.CategoryTheory.InducedCategory
import Structure.v1.Atlas.TensorCategories.code.Proposition_2_12_2
set_option maxHeartbeats 800000
set_option linter.all false

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory

/-- The category structure on right-exact module functors, induced from the
ambient category of module functors via the forgetful map. -/
instance rightExactModuleFunctorCategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M]
    (N : Type u₃) [Category.{v₃} N] [LeftModuleCategory C N] :
    Category (RightExactModuleFunctor C M N) :=
  inferInstanceAs (Category (InducedCategory _ RightExactModuleFunctor.toModuleFunctor))

end CategoryTheory
