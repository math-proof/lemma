/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
public import Theorem.Category.Atlas.v1.TensorCategories.code.PivotalSpherical
public import Class.v1.Atlas.TensorCategories.code.SemisimpleMultitensor
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

public section

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
