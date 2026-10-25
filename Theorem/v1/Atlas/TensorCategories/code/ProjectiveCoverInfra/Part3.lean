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
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Def.v1.Atlas.TensorCategories.code.ProjectiveCoverInfra.Part3
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category Limits

universe v u w


noncomputable section

namespace ProjectiveCoverInfra

set_option linter.unusedSectionVars false

variable (𝕜 : Type w) [Field 𝕜]

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear 𝕜 C]

section Augmentation

variable {P S : C}

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

end Augmentation
end ProjectiveCoverInfra
end
