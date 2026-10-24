/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_2_9_21.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.ExactModuleCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Mathlib.CategoryTheory.Monoidal.Mod_

set_option maxHeartbeats 800000

universe v₁ u₁

namespace CategoryTheory

open Category MonoidalCategory

/-- Definition 2.9.21 (exact algebra): an algebra object `A` in a monoidal category `C`
is exact when the category of left `A`-modules is an exact module category over `C`. -/
def IsExactAlgebra
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (A : C) [MonObj A] : Prop :=
  Nonempty (ExactModuleCategory C (Mod_ C A))

end CategoryTheory
