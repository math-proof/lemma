/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FittingLemmaInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.TensorCategories.code.FittingLemmaLocalEnd
import Lemma.Category.Atlas.v1.TensorCategories.code.FittingLemmaLocalEnd
import Lemma.Category.Atlas.v1.TensorCategories.code.FittingAlgebraLocalRing
import Theorem.v1.Atlas.TensorCategories.code.FittingAlgebraLocalRing
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

universe v u w


namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An indecomposable object in an abelian (idempotent-complete) category has only the
trivial idempotent endomorphisms, namely `0` and the identity. The proof splits the
idempotent `e` and its complement `1 - e` via the idempotent-completion to exhibit `P`
as a binary biproduct, then applies indecomposability. -/
lemma idem_trivial_of_indecomposable {P : C}
    (hP : Indecomposable P) (e : P ⟶ P) (he : e ≫ e = e) :
    e = 0 ∨ e = 𝟙 P := by
  obtain ⟨Y, i, s, his, hsi⟩ := (inferInstance : IsIdempotentComplete C).idempotents_split P e he
  obtain ⟨Z, j, t, hjt, htj⟩ := (inferInstance : IsIdempotentComplete C).idempotents_split
    P (𝟙 P - e) (idem_of_id_sub_idem e he)
  have hi_e : i ≫ e = i := by rw [← hsi, ← Category.assoc, his, Category.id_comp]
  have hj_e : j ≫ e = 0 := by
    have : j ≫ (𝟙 P - e) = j := by rw [← htj, ← Category.assoc, hjt, Category.id_comp]
    rwa [Preadditive.comp_sub, Category.comp_id, sub_eq_self] at this
  have h_it : i ≫ t = 0 := by
    have h1 : i ≫ (𝟙 P - e) = 0 := by
      rw [Preadditive.comp_sub, hi_e, Category.comp_id, sub_self]
    have h2 : (i ≫ t) ≫ j = 0 := by rw [Category.assoc, htj, h1]
    have h3 : (i ≫ t) ≫ (j ≫ t) = 0 := by rw [← Category.assoc, h2, zero_comp]
    rwa [hjt, Category.comp_id] at h3
  have h_js : j ≫ s = 0 := by
    have h2 : (j ≫ s) ≫ i = 0 := by rw [Category.assoc, hsi, hj_e]
    have h3 : (j ≫ s) ≫ (i ≫ s) = 0 := by rw [← Category.assoc, h2, zero_comp]
    rwa [his, Category.comp_id] at h3
  let bc := BinaryBicone.mk P s t i j his h_it h_js hjt
  have hbl := isBinaryBilimitOfTotal bc (by rw [hsi, htj, add_sub_cancel])
  haveI : HasBinaryBiproduct Y Z := HasBinaryBiproduct.mk ⟨bc, hbl⟩
  rcases hP.2 Y Z (biprod.uniqueUpToIso Y Z hbl) with hY0 | hZ0
  · exact Or.inl (by rw [← hsi, hY0.eq_of_src i _, comp_zero])
  · exact Or.inr ((sub_eq_zero.mp (by rw [← htj, hZ0.eq_of_src j _, comp_zero])).symm)

end
end CategoryTheory
