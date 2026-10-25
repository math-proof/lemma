/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_2_11_2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Equivalence
set_option maxHeartbeats 800000

set_option autoImplicit false

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory

/-- Internal algebra object in a monoidal category `C`: an object equipped with a
multiplication and unit morphism. -/
structure AlgObj₂ (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] where
  carrier : C
  mul : carrier ⊗ carrier ⟶ carrier
  unit : 𝟙_ C ⟶ carrier

/-- Right module object over an internal algebra `A` in a monoidal category: an
object `obj` of `C` together with a right action `obj ⊗ A.carrier ⟶ obj`. -/
structure RModObj₂ {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    (A : AlgObj₂ C) where
  obj : C
  act : obj ⊗ A.carrier ⟶ obj

end CategoryTheory
