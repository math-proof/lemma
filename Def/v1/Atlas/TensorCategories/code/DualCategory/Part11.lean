/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Abbrev.v1.Atlas.TensorCategories.code.IndecomposableModuleCat
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_
import Theorem.v1.Atlas.TensorCategories.code.DualCategory.Part9
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

variable (M : Type u) [Category.{v} M] [LeftModuleCategory C M]

attribute [reassoc] DrinfeldCenterHalfBraidingHom.comm

/-- Identity morphism on a half-braiding object of the Drinfeld center. -/
def DrinfeldCenterHalfBraidingHom.id {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (P : DrinfeldCenterHalfBraidingObj C) : DrinfeldCenterHalfBraidingHom P P where
  hom := 𝟙 P.X
  comm V := by simp

/-- Composition of half-braiding morphisms in the Drinfeld center. -/
def DrinfeldCenterHalfBraidingHom.comp {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {P Q R : DrinfeldCenterHalfBraidingObj C}
    (f : DrinfeldCenterHalfBraidingHom P Q) (g : DrinfeldCenterHalfBraidingHom Q R) :
    DrinfeldCenterHalfBraidingHom P R where
  hom := f.hom ≫ g.hom
  comm V := by
    simp only [MonoidalCategory.whiskerLeft_comp, assoc]
    rw [g.comm]
    simp only [← assoc]
    rw [f.comm]
    simp only [assoc, comp_whiskerRight]

end CategoryTheory
