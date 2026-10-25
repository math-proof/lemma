/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Lemma_2_14_7.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_
set_option linter.unusedSimpArgs false

universe u v

open CategoryTheory MonoidalCategory


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

open HasLeftDual HasRightDual ExactPairing MonObj

namespace Lemma2147

/-- The canonical algebra multiplication on `ᘁA ⊗ A` for an object `A` with a left dual,
defined by inserting the evaluation `ε_ (ᘁA) A` in the middle. -/
noncomputable def dualAlgMul (A : C) [HasLeftDual A] :
    ((ᘁA : C) ⊗ A) ⊗ ((ᘁA : C) ⊗ A) ⟶ (ᘁA : C) ⊗ A :=
  (α_ (ᘁA : C) A ((ᘁA : C) ⊗ A)).hom ≫
  (ᘁA : C) ◁ ((α_ A (ᘁA : C) A).inv ≫ (ε_ (ᘁA : C) A ▷ A) ≫ (λ_ A).hom)

end Lemma2147
end CategoryTheory
