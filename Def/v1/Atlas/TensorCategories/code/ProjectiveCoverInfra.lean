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
import Instance.v1.Atlas.TensorCategories.code.ProjectiveCoverInfra
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category Limits

universe v u w


noncomputable section

namespace ProjectiveCoverInfra

set_option linter.unusedSectionVars false

variable (𝕜 : Type w) [Field 𝕜]

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear 𝕜 C]

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

end ProjectiveCoverInfra
end
