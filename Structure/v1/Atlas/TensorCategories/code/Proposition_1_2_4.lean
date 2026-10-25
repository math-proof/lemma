/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_2_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory

universe v u


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A version of "unit object" data: an object `U` together with natural isomorphisms
identifying `tensorLeft U` and `tensorRight U` with the identity functor, and satisfying the
triangle axiom relating them via the associator. -/
structure IsUnitObject' (U : C) where
  rightUnitor' : tensorRight U ≅ Functor.id C
  leftUnitor' : tensorLeft U ≅ Functor.id C
  triangle' : ∀ (X Y : C),
    (α_ X U Y).hom ≫ X ◁ (leftUnitor'.hom.app Y) = (rightUnitor'.hom.app X) ▷ Y

end CategoryTheory
