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
import Def.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part3
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v u


noncomputable section

namespace CategoryTheory

section UnitSemisimple

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

section ComponentSubcategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

/-- Proposition 1.15.5 (2): tensor products between component subcategories vanish off the
diagonal — `C_{ij} ⊗ C_{kl} = 0` unless `j = k`. -/
theorem tensor_component_zero
    [Preadditive C] [MonoidalPreadditive C]
    {n : ℕ} (f : Fin n → C) [HasBiproduct f]
    (hiso : 𝟙_ C ≅ ⨁ f) (hsimp : ∀ i, Simple (f i))
    (X Y : C) (i j k l : Fin n) (hjk : j ≠ k) :
    IsZero (componentObj f X i j ⊗ componentObj f Y k l) := by
  unfold componentObj


  have iso : (f i ⊗ (X ⊗ f j)) ⊗ (f k ⊗ (Y ⊗ f l)) ≅
      (f i ⊗ X) ⊗ ((f j ⊗ f k) ⊗ (Y ⊗ f l)) :=
    (whiskerRightIso (α_ (f i) X (f j)).symm (f k ⊗ (Y ⊗ f l))) ≪≫
    (α_ (f i ⊗ X) (f j) (f k ⊗ (Y ⊗ f l))) ≪≫
    (whiskerLeftIso (f i ⊗ X) (α_ (f j) (f k) (Y ⊗ f l)).symm)

  have hzero : IsZero (f j ⊗ f k) := unitComponent_tensor_zero f hiso hsimp hjk

  exact (isZero_tensor_right (isZero_tensor_left hzero)).of_iso iso

end ComponentSubcategories
end UnitSemisimple
end CategoryTheory
end
