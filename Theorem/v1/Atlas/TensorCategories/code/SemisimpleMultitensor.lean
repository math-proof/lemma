/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.PivotalSpherical
import Class.v1.Atlas.TensorCategories.code.SemisimpleMultitensor
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v u


noncomputable section

namespace CategoryTheory

section UnitSemisimple

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

lemma isZero_tensor_left {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [Preadditive C] [MonoidalPreadditive C] {A B : C} (h : IsZero A) :
    IsZero (A ⊗ B) := by
  rw [IsZero.iff_id_eq_zero]
  have hA : 𝟙 A = 0 := h.eq_of_src (𝟙 A) 0
  have : 𝟙 (A ⊗ B) = 𝟙 A ▷ B ≫ A ◁ 𝟙 B := by simp
  rw [this, hA]
  simp [MonoidalPreadditive.zero_whiskerRight]

lemma isZero_tensor_right {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [Preadditive C] [MonoidalPreadditive C] {A B : C} (h : IsZero B) :
    IsZero (A ⊗ B) := by
  rw [IsZero.iff_id_eq_zero]
  have hB : 𝟙 B = 0 := h.eq_of_src (𝟙 B) 0
  have : 𝟙 (A ⊗ B) = 𝟙 A ▷ B ≫ A ◁ 𝟙 B := by simp
  rw [this, hB]
  simp [MonoidalPreadditive.whiskerLeft_zero]

end UnitSemisimple
end CategoryTheory
end
