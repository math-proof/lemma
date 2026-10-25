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
import Abbrev.v1.Atlas.TensorCategories.code.SemisimpleMultitensor
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v u


noncomputable section

namespace CategoryTheory

section UnitSemisimple

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

section ComponentSubcategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

omit [HasZeroMorphisms C] in
/-- Coherence helper: the chain through the unitors and a whiskering collapses to the
composition `s ≫ r`. -/
lemma whisker_unitor_calc {A B : C} (s : A ⟶ 𝟙_ C) (r : 𝟙_ C ⟶ B) :
    (ρ_ A).inv ≫ A ◁ r ≫ s ▷ B ≫ (λ_ B).hom = s ≫ r := by
  slice_lhs 2 3 => rw [whisker_exchange s r]
  slice_lhs 1 2 => rw [← rightUnitor_inv_naturality]
  slice_lhs 3 4 => rw [leftUnitor_naturality]
  slice_lhs 2 3 => rw [unitors_equal, Iso.inv_hom_id]
  simp

/-- If `𝟙_ C` decomposes as a sum of distinct simple summands `f i`, then the cross tensor
products `f i ⊗ f j` with `i ≠ j` are zero. -/
theorem unitComponent_tensor_zero {n : ℕ} (f : Fin n → C) [HasBiproduct f]
    (hiso : 𝟙_ C ≅ ⨁ f) (hsimp : ∀ i, Simple (f i))
    {i j : Fin n} (hij : i ≠ j) :
    IsZero (f i ⊗ f j) := by

  let r_i : 𝟙_ C ⟶ f i := hiso.hom ≫ biproduct.π f i
  let s_i : f i ⟶ 𝟙_ C := biproduct.ι f i ≫ hiso.inv
  let r_j : 𝟙_ C ⟶ f j := hiso.hom ≫ biproduct.π f j
  let s_j : f j ⟶ 𝟙_ C := biproduct.ι f j ≫ hiso.inv

  have s_r_i : s_i ≫ r_i = 𝟙 (f i) := by
    simp [s_i, r_i, Category.assoc, Iso.inv_hom_id_assoc]
  have s_r_j : s_j ≫ r_j = 𝟙 (f j) := by
    simp [s_j, r_j, Category.assoc, Iso.inv_hom_id_assoc]

  let ret : f i ⊗ f j ⟶ f j := s_i ▷ (f j) ≫ (λ_ (f j)).hom
  let sec : f j ⟶ f i ⊗ f j := (λ_ (f j)).inv ≫ r_i ▷ (f j)

  let ret' : f i ⊗ f j ⟶ f i := (f i) ◁ s_j ≫ (ρ_ (f i)).hom
  let sec' : f i ⟶ f i ⊗ f j := (ρ_ (f i)).inv ≫ (f i) ◁ r_j

  have retract_id : ret ≫ sec = 𝟙 (f i ⊗ f j) := by
    simp only [ret, sec, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← MonoidalCategory.comp_whiskerRight, s_r_i, MonoidalCategory.id_whiskerRight]

  have retract_id' : ret' ≫ sec' = 𝟙 (f i ⊗ f j) := by
    simp only [ret', sec', Category.assoc, Iso.hom_inv_id_assoc]
    rw [← MonoidalCategory.whiskerLeft_comp, s_r_j, MonoidalCategory.whiskerLeft_id]

  have ret_mono : Mono ret := (SplitMono.mk sec retract_id).mono

  have h_sec'_ret_zero : sec' ≫ ret = 0 := by
    simp only [sec', ret, Category.assoc]
    rw [whisker_unitor_calc s_i r_j]
    simp only [s_i, r_j, Category.assoc, Iso.inv_hom_id_assoc]
    exact biproduct.ι_π_ne (f := f) hij

  rw [IsZero.iff_id_eq_zero]
  by_cases h_ret : IsIso ret
  ·
    have hsec'_zero : sec' = 0 := by rw [← cancel_mono ret]; simp [h_sec'_ret_zero]
    calc 𝟙 (f i ⊗ f j) = ret' ≫ sec' := retract_id'.symm
      _ = ret' ≫ 0 := by rw [hsec'_zero]
      _ = 0 := by simp
  ·
    have hret_zero : ret = 0 := by
      rwa [Simple.mono_isIso_iff_nonzero ret, not_not] at h_ret
    calc 𝟙 (f i ⊗ f j) = ret ≫ sec := retract_id.symm
      _ = 0 ≫ sec := by rw [hret_zero]
      _ = 0 := by simp

end ComponentSubcategories
end UnitSemisimple
end CategoryTheory
end
