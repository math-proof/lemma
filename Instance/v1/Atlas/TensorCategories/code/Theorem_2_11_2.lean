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
import Structure.v1.Atlas.TensorCategories.code.Theorem_2_11_2.Part2
set_option maxHeartbeats 800000

set_option autoImplicit false

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory

attribute [reassoc (attr := simp)] RModHom₂.comm

/-- Category structure on `ModC₂ A`, the category of right `A`-modules in `C`. -/
instance modC₂_category {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    (A : AlgObj₂ C) : Category.{v₁} (ModC₂ A) where
  Hom M N := RModHom₂ M N
  id M := { hom := 𝟙 M.obj, comm := by simp }
  comp f g := {
    hom := f.hom ≫ g.hom
    comm := by
      simp only [comp_whiskerRight, assoc]
      rw [g.comm, ← assoc, f.comm, assoc]
  }
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp [assoc]

end CategoryTheory
