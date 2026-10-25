/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Lemma_1_51_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Def.v1.Atlas.TensorCategories.code.Lemma_1_51_1
open CategoryTheory MonoidalCategory Category

universe v u


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable [RigidCategory C]

variable (C) in
/-- Data witnessing the existence of a distinguished invertible object in `C`, packaging
a chosen object `distinguished : C` together with isomorphisms `P** ≅ distinguished ⊗ P` for
every projective `P` and a self-isomorphism `distinguished** ≅ distinguished`. This is the
hypothesis structure for Lemma 1.51.1 of EGNO. -/
class HasDistinguishedInvertibleData_1_51 where
  distinguished : C
  doubleDual_iso_tensor : ∀ (P : C) [Projective P],
    Nonempty (doubleDual_1_51 P ≅ distinguished ⊗ P)
  doubleDual_self : Nonempty (doubleDual_1_51 distinguished ≅ distinguished)

end CategoryTheory
