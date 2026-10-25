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
import Def.v1.Atlas.TensorCategories.code.ProjectiveCoverInfra
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category Limits

universe v u w


noncomputable section

namespace ProjectiveCoverInfra

set_option linter.unusedSectionVars false

variable (𝕜 : Type w) [Field 𝕜]

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear 𝕜 C]

/-- Action of `postcomp` on a hom is given by postcomposition. -/
@[simp] theorem postcomp_apply (P : C) {Y Z : C} (f : Y ⟶ Z) (h : P ⟶ Y) :
    postcomp 𝕜 P f h = h ≫ f := rfl

/-- Action of `precomp` on a hom is given by precomposition. -/
@[simp] theorem precomp_apply (P : C) (a : P ⟶ P) (X : C) (h : P ⟶ X) :
    precomp 𝕜 P a X h = a ≫ h := rfl

end ProjectiveCoverInfra
end
