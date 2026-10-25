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
import Theorem.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part2
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v u


noncomputable section

namespace CategoryTheory

section UnitSemisimple

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

section ComponentSubcategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

/-- When `𝟙_ C` decomposes as a sum of distinct simple summands `f i`, each diagonal
component `f i ⊗ f i` is canonically isomorphic to `f i`. -/
def component_diagonal_unit_iso {n : ℕ} (f : Fin n → C) [HasBiproduct f]
    (hiso : 𝟙_ C ≅ ⨁ f) (hsimp : ∀ i, Simple (f i))
    (i : Fin n) :
    f i ⊗ f i ≅ f i := by
  haveI : Simple (f i) := hsimp i

  let r_i : 𝟙_ C ⟶ f i := hiso.hom ≫ biproduct.π f i
  let s_i : f i ⟶ 𝟙_ C := biproduct.ι f i ≫ hiso.inv

  have s_r_i : s_i ≫ r_i = 𝟙 (f i) := by
    simp [s_i, r_i, Category.assoc, Iso.inv_hom_id_assoc]

  let ret : f i ⊗ f i ⟶ f i := s_i ▷ (f i) ≫ (λ_ (f i)).hom
  let sec : f i ⟶ f i ⊗ f i := (λ_ (f i)).inv ≫ r_i ▷ (f i)

  have retract_id : ret ≫ sec = 𝟙 (f i ⊗ f i) := by
    simp only [ret, sec, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← MonoidalCategory.comp_whiskerRight, s_r_i, MonoidalCategory.id_whiskerRight]

  let sec' : f i ⟶ f i ⊗ f i := (ρ_ (f i)).inv ≫ (f i) ◁ r_i

  have cross_id : sec' ≫ ret = 𝟙 (f i) := by
    simp only [sec', ret, Category.assoc]
    rw [whisker_unitor_calc s_i r_i]
    exact s_r_i

  have ret_mono : Mono ret := (SplitMono.mk sec retract_id).mono

  have ret_nonzero : ret ≠ 0 := by
    intro h
    have : 𝟙 (f i) = 0 := by rw [← cross_id, h, Limits.comp_zero]
    exact id_nonzero (f i) this

  have ret_iso : IsIso ret := (Simple.mono_isIso_iff_nonzero ret).mpr ret_nonzero
  exact asIso ret


end ComponentSubcategories
end UnitSemisimple
end CategoryTheory
end
