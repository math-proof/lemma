/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ProjectiveCoverInfra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
public import Theorem.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
public import Def.v1.Atlas.TensorCategories.code.ProjectiveCoverInfra
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category Limits

public section

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
