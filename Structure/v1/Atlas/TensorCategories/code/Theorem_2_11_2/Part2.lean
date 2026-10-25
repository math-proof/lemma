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
import Def.v1.Atlas.TensorCategories.code.Theorem_2_11_2
set_option maxHeartbeats 800000

set_option autoImplicit false

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory

/-- Morphism of right `A`-modules in `C`: a morphism `M.obj ⟶ N.obj` in `C` that
intertwines the right `A`-actions. -/
@[ext]
structure RModHom₂ {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {A : AlgObj₂ C} (M N : RModObj₂ A) where
  hom : M.obj ⟶ N.obj
  comm : (hom ▷ A.carrier) ≫ N.act = M.act ≫ hom := by aesop_cat

end CategoryTheory
