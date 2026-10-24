/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ProjectiveCoverInfra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import sympy.atlas.v1.Atlas.TensorCategories.code.FiniteTensorCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category Limits

universe v u w

noncomputable section

namespace ProjectiveCoverInfra

set_option linter.unusedSectionVars false

variable (𝕜 : Type w) [Field 𝕜]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear 𝕜 C]

/-- The endomorphism algebra of a finite-dimensional hom space is finite-dimensional. -/
instance endFiniteDimensional (X : C) [FiniteDimensional 𝕜 (X ⟶ X)] :
    FiniteDimensional 𝕜 (End X) :=
  ‹FiniteDimensional 𝕜 (X ⟶ X)›

/-- Postcomposition by a fixed morphism `f : Y ⟶ Z` as a `𝕜`-linear map `(P ⟶ Y) → (P ⟶ Z)`. -/
def postcomp (P : C) {Y Z : C} (f : Y ⟶ Z) : (P ⟶ Y) →ₗ[𝕜] (P ⟶ Z) where
  toFun h := h ≫ f
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _
  map_smul' r h := by show (r • h) ≫ f = r • (h ≫ f); rw [Linear.smul_comp]

/-- Precomposition by a fixed endomorphism `a : P ⟶ P` as a `𝕜`-linear map
`(P ⟶ X) → (P ⟶ X)`. -/
def precomp (P : C) (a : P ⟶ P) (X : C) : (P ⟶ X) →ₗ[𝕜] (P ⟶ X) where
  toFun h := a ≫ h
  map_add' g g' := Preadditive.comp_add _ _ _ a g g'
  map_smul' r h := by show a ≫ (r • h) = r • (a ≫ h); rw [Linear.comp_smul]

/-- Action of `postcomp` on a hom is given by postcomposition. -/
@[simp] theorem postcomp_apply (P : C) {Y Z : C} (f : Y ⟶ Z) (h : P ⟶ Y) :
    postcomp 𝕜 P f h = h ≫ f := rfl

/-- Action of `precomp` on a hom is given by precomposition. -/
@[simp] theorem precomp_apply (P : C) (a : P ⟶ P) (X : C) (h : P ⟶ X) :
    precomp 𝕜 P a X h = a ≫ h := rfl

section HomDimension

variable [Abelian C]

end HomDimension

section ProjectiveCoverEnd

variable [Abelian C]

end ProjectiveCoverEnd

section Augmentation

variable {P S : C}

/-- When `(P ⟶ S)` is one-dimensional, the unique scalar `c` such that `f = c • π`. -/
def homScalar (hdim : Module.finrank 𝕜 (P ⟶ S) = 1)
    (π : P ⟶ S) (hπ : π ≠ 0) (f : P ⟶ S) : 𝕜 :=
  (exists_smul_eq_of_finrank_eq_one hdim hπ f).choose

/-- Defining property of `homScalar`: `f = homScalar f • π`. -/
theorem homScalar_spec (hdim : Module.finrank 𝕜 (P ⟶ S) = 1)
    (π : P ⟶ S) (hπ : π ≠ 0) (f : P ⟶ S) :
    f = homScalar 𝕜 hdim π hπ f • π :=
  ((exists_smul_eq_of_finrank_eq_one hdim hπ f).choose_spec).symm

/-- Scalars acting on a nonzero hom are determined by their action: `c • π = d • π` implies
`c = d`. -/
theorem smul_π_injective (π : P ⟶ S) (hπ : π ≠ 0)
    {c d : 𝕜} (h : c • π = d • π) : c = d := by
  have hsub : (c - d) • π = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp hsub with hcd | habs
  · exact sub_eq_zero.mp hcd
  · exact absurd habs hπ

/-- For an endomorphism `a : End P`, the scalar `c` such that `a ≫ π = c • π`. -/
def precompScalar (hdim : Module.finrank 𝕜 (P ⟶ S) = 1)
    (π : P ⟶ S) (hπ : π ≠ 0) (a : End P) : 𝕜 :=
  homScalar 𝕜 hdim π hπ (a ≫ π)

/-- Defining property of `precompScalar`: `a ≫ π = precompScalar a • π`. -/
theorem precompScalar_spec (hdim : Module.finrank 𝕜 (P ⟶ S) = 1)
    (π : P ⟶ S) (hπ : π ≠ 0) (a : End P) :
    a ≫ π = precompScalar 𝕜 hdim π hπ a • π :=
  homScalar_spec 𝕜 hdim π hπ (a ≫ π)

/-- `precompScalar` is multiplicative: `precompScalar (a*b) = precompScalar a *
precompScalar b`. -/
theorem precompScalar_mul (hdim : Module.finrank 𝕜 (P ⟶ S) = 1)
    (π : P ⟶ S) (hπ : π ≠ 0) (a b : End P) :
    precompScalar 𝕜 hdim π hπ (a * b) =
    precompScalar 𝕜 hdim π hπ a * precompScalar 𝕜 hdim π hπ b := by
  apply smul_π_injective 𝕜 π hπ
  rw [mul_smul, ← precompScalar_spec 𝕜 hdim π hπ b,
      ← Linear.comp_smul, ← precompScalar_spec 𝕜 hdim π hπ a,
      ← assoc]
  exact (precompScalar_spec 𝕜 hdim π hπ (a * b)).symm

/-- `precompScalar` is additive. -/
theorem precompScalar_add (hdim : Module.finrank 𝕜 (P ⟶ S) = 1)
    (π : P ⟶ S) (hπ : π ≠ 0) (a b : End P) :
    precompScalar 𝕜 hdim π hπ (a + b) =
    precompScalar 𝕜 hdim π hπ a + precompScalar 𝕜 hdim π hπ b := by
  apply smul_π_injective 𝕜 π hπ
  rw [add_smul, ← precompScalar_spec 𝕜 hdim π hπ a,
      ← precompScalar_spec 𝕜 hdim π hπ b,
      ← precompScalar_spec 𝕜 hdim π hπ (a + b)]
  exact Preadditive.add_comp _ _ _ a b π

/-- `precompScalar` sends the identity endomorphism to `1`. -/
theorem precompScalar_one (hdim : Module.finrank 𝕜 (P ⟶ S) = 1)
    (π : P ⟶ S) (hπ : π ≠ 0) :
    precompScalar 𝕜 hdim π hπ (1 : End P) = 1 := by
  apply smul_π_injective 𝕜 π hπ
  rw [one_smul, ← precompScalar_spec]
  exact id_comp π

/-- `precompScalar` sends the zero endomorphism to `0`. -/
theorem precompScalar_zero (hdim : Module.finrank 𝕜 (P ⟶ S) = 1)
    (π : P ⟶ S) (hπ : π ≠ 0) :
    precompScalar 𝕜 hdim π hπ (0 : End P) = 0 := by
  apply smul_π_injective 𝕜 π hπ
  rw [zero_smul, ← precompScalar_spec]
  exact zero_comp

/-- The augmentation `End P → 𝕜` packaged as a ring homomorphism, built from
`precompScalar`. -/
def augmentationRingHom (hdim : Module.finrank 𝕜 (P ⟶ S) = 1)
    (π : P ⟶ S) (hπ : π ≠ 0) :
    End P →+* 𝕜 where
  toFun := precompScalar 𝕜 hdim π hπ
  map_one' := precompScalar_one 𝕜 hdim π hπ
  map_mul' := precompScalar_mul 𝕜 hdim π hπ
  map_zero' := precompScalar_zero 𝕜 hdim π hπ
  map_add' := precompScalar_add 𝕜 hdim π hπ

/-- The augmentation `End P → 𝕜` upgraded to a `𝕜`-algebra homomorphism. -/
def augmentation (hdim : Module.finrank 𝕜 (P ⟶ S) = 1)
    (π : P ⟶ S) (hπ : π ≠ 0) :
    End P →ₐ[𝕜] 𝕜 where
  toRingHom := augmentationRingHom 𝕜 hdim π hπ
  commutes' r := by
    show precompScalar 𝕜 hdim π hπ (algebraMap 𝕜 (End P) r) = algebraMap 𝕜 𝕜 r
    apply smul_π_injective 𝕜 π hπ
    rw [← precompScalar_spec, Algebra.algebraMap_eq_smul_one]
    show (r • 𝟙 P) ≫ π = r • π
    rw [Linear.smul_comp, id_comp]

end Augmentation

end ProjectiveCoverInfra
