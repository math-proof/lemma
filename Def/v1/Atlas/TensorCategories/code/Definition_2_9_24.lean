/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_2_9_24.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.IndecomposableModuleCat
import Mathlib.CategoryTheory.Monoidal.Bimod
import Mathlib.CategoryTheory.Monoidal.Mod_
import Abbrev.v1.Atlas.TensorCategories.code.Definition_2_9_24
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An algebra `A ∈ C` is indecomposable when its category of left modules is
indecomposable as a left `C`-module category. -/
def IsIndecomposableAlgebra (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (A : C) [MonObj A]
    [LeftModuleCategory C (Mod_ C A)] : Prop :=
  IsIndecomposableModuleCategory C (Mod_ C A)

end CategoryTheory
