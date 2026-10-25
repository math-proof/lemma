/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InvertibleObjects.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Subcategory
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

universe v u


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An object `X` of a monoidal category `C` is invertible if there exists an object
`tensorInverse` together with isomorphisms `X ⊗ tensorInverse ≅ 𝟙_ C` and
`tensorInverse ⊗ X ≅ 𝟙_ C` (cf. Definition 1.11.1). -/
class IsInvertibleObject (X : C) where
  tensorInverse : C
  compIso : X ⊗ tensorInverse ≅ 𝟙_ C
  invCompIso : tensorInverse ⊗ X ≅ 𝟙_ C

end CategoryTheory
