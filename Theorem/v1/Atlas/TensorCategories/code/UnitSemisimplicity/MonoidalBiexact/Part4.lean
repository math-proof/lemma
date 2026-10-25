/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleRing.Field
import Mathlib.RingTheory.Artinian.Module
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import Mathlib.RingTheory.Idempotents
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Tactic.CategoryTheory.Slice
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Instance.v1.Atlas.TensorCategories.code.UnitSemisimplicity.MonoidalBiexact.Part3
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

universe v u w


noncomputable section

namespace TensorCategories

section TensorBiexact

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalBiexact C]

/-- In a monoidally biexact abelian category, the tensor product of two monomorphisms
is a monomorphism. -/
lemma tensorHom_mono_of_mono {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    [Mono f] [Mono g] : Mono (f ⊗ₘ g) := by
  have h : f ⊗ₘ g = f ▷ X₂ ≫ Y₁ ◁ g := MonoidalCategory.tensorHom_def f g
  rw [h]
  haveI : Mono (f ▷ X₂) := MonoidalBiexact.whiskerRight_mono f X₂
  haveI : Mono (Y₁ ◁ g) := MonoidalBiexact.whiskerLeft_mono Y₁ g
  exact mono_comp _ _

/-- In a monoidally biexact abelian category, the tensor product of two epimorphisms
is an epimorphism. -/
lemma tensorHom_epi_of_epi {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    [Epi f] [Epi g] : Epi (f ⊗ₘ g) := by
  have h : f ⊗ₘ g = f ▷ X₂ ≫ Y₁ ◁ g := MonoidalCategory.tensorHom_def f g
  rw [h]
  haveI : Epi (f ▷ X₂) := MonoidalBiexact.whiskerRight_epi f X₂
  haveI : Epi (Y₁ ◁ g) := MonoidalBiexact.whiskerLeft_epi Y₁ g
  exact epi_comp _ _

end TensorBiexact

/-- If an epi `e : A ⟶ B` followed by a mono `m : B ⟶ D` is the zero morphism, then
the intermediate object `B` is zero. -/
lemma isZero_of_epi_comp_mono_eq_zero {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : C} (e : A ⟶ B) (m : B ⟶ D)
    [Epi e] [Mono m] (h : e ≫ m = 0) : IsZero B := by
  have he : e = 0 := by rwa [← cancel_mono m, zero_comp]
  rw [IsZero.iff_id_eq_zero]
  exact (Preadditive.epi_iff_cancel_zero e).mp inferInstance B (𝟙 B) (by rw [he, zero_comp])

section TensorBiexactCont

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalBiexact C]

/-- In a monoidally biexact abelian category, if `f ⊗ₘ f = 0` for an endomorphism `f`
of the unit, then `f = 0`. The proof factors `f` through its abelian image and uses
biexactness to conclude the image is zero. -/
theorem tensorImage_zero_of_tensorHom_zero {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [MonoidalBiexact C]
    (f : 𝟙_ C ⟶ 𝟙_ C) (hf : f ⊗ₘ f = 0) : f = 0 := by

  have hfac : Abelian.factorThruImage f ≫ Abelian.image.ι f = f := Abelian.image.fac f

  have htensor : (Abelian.factorThruImage f ⊗ₘ Abelian.factorThruImage f) ≫
      (Abelian.image.ι f ⊗ₘ Abelian.image.ι f) = 0 := by
    rw [tensorHom_comp_tensorHom, hfac, hf]

  haveI : Epi (Abelian.factorThruImage f ⊗ₘ Abelian.factorThruImage f) :=
    tensorHom_epi_of_epi _ _
  haveI : Mono (Abelian.image.ι f ⊗ₘ Abelian.image.ι f) :=
    tensorHom_mono_of_mono _ _

  have hJJ : IsZero (Abelian.image f ⊗ Abelian.image f) :=
    isZero_of_epi_comp_mono_eq_zero _ _ htensor

  have hJ : IsZero (Abelian.image f) :=
    MonoidalBiexact.isZero_of_tensorObj_self_isZero _ hJJ

  rw [← hfac, hJ.eq_of_src (Abelian.image.ι f) 0, comp_zero]

end TensorBiexactCont

/-- A monoid-with-zero in which every square-zero element is zero is reduced
(has no nonzero nilpotent elements). The proof uses strong induction to reduce
nilpotency to the square-zero case. -/
lemma isReduced_of_sq_zero {R : Type*} [MonoidWithZero R]
    (h : ∀ x : R, x * x = 0 → x = 0) : IsReduced R := by
  apply IsReduced.mk
  intro x ⟨n, hn⟩
  suffices ∀ (m : ℕ) (y : R), y ^ m = 0 → y = 0 from this n x hn
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro y hym
    by_cases hm : m ≤ 1
    · interval_cases m
      · simp [pow_zero] at hym
        have : (0 : R) = 1 := hym.symm
        rw [show y = y * 1 from (mul_one y).symm, ← this, mul_zero]
      · simpa [pow_one] using hym
    · push Not at hm
      set k := (m + 1) / 2
      have hk_lt : k < m := by omega
      have hk_ge : m ≤ k + k := by omega
      have hsq : (y ^ k) * (y ^ k) = 0 := by
        rw [← pow_add]
        exact pow_eq_zero_of_le hk_ge hym
      exact ih k hk_lt y (h _ hsq)

/-- In a monoidally biexact abelian monoidal category, the endomorphism ring of the
unit object is reduced. -/
theorem endUnit_isReduced {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [Abelian C] [MonoidalBiexact C] : IsReduced (End (𝟙_ C)) := by
  apply isReduced_of_sq_zero
  intro f hf

  have hff : f ≫ f = 0 := hf

  have htensor : f ⊗ₘ f = 0 := tensorHom_sq_of_sq_zero f hff

  exact tensorImage_zero_of_tensorHom_zero f htensor

/-- Under the standing assumptions (monoidally biexact, Artinian endomorphism ring),
the commutative ring `End(𝟙_ C)` is semisimple. -/
theorem endUnit_isSemisimpleRing {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [inst_ab : Abelian C] [MonoidalBiexact C]
    [IsArtinianRing (End (𝟙_ C))] :
    IsSemisimpleRing (End (𝟙_ C)) :=
  @IsArtinianRing.isSemisimpleRing_of_isReduced (End (𝟙_ C))
    (@endUnit_commRing C _ _ inst_ab.toPreadditive)
    inferInstance endUnit_isReduced

end TensorCategories
end
