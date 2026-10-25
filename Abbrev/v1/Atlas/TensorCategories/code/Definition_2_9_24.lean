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
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Definition 2.9.24: an `(A, B)`-bimodule in `C`, i.e. an object of `Bimod A B`. -/
abbrev Definition_2_9_24_Bimodule (A B : Mon C) := Bimod A B

/-- Underlying object of an `(A, B)`-bimodule. -/
abbrev Definition_2_9_24_Bimodule.obj {A B : Mon C}
    (M : Definition_2_9_24_Bimodule A B) : C := M.X

/-- Left action `A ⊗ M ⟶ M` of an `(A, B)`-bimodule. -/
abbrev Definition_2_9_24_Bimodule.leftAction {A B : Mon C}
    (M : Definition_2_9_24_Bimodule A B) : A.X ⊗ M.X ⟶ M.X :=
  M.actLeft

/-- Right action `M ⊗ B ⟶ M` of an `(A, B)`-bimodule. -/
abbrev Definition_2_9_24_Bimodule.rightAction {A B : Mon C}
    (M : Definition_2_9_24_Bimodule A B) : M.X ⊗ B.X ⟶ M.X :=
  M.actRight

end CategoryTheory
