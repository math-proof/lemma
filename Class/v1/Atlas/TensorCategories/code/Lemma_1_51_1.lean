/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Lemma_1_51_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
open CategoryTheory MonoidalCategory Category

universe v u


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An object `X` of a monoidal category is invertible (in the sense of Section 1.51) if there
exists a tensor inverse `tensorInverse` and isomorphisms exhibiting `X ⊗ tensorInverse ≅ 𝟙_ C`
and `tensorInverse ⊗ X ≅ 𝟙_ C`. -/
class IsInvertibleObject_1_51 (X : C) where
  tensorInverse : C
  compIso : X ⊗ tensorInverse ≅ 𝟙_ C
  invCompIso : tensorInverse ⊗ X ≅ 𝟙_ C

end CategoryTheory
