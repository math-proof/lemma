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
public import Theorem.v1.Atlas.TensorCategories.code.ProjectiveCoverInfra.Part2
set_option maxHeartbeats 800000
open CategoryTheory MonoidalCategory Category Limits


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ProjectiveCoverInfra.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe v u w


noncomputable section

namespace ProjectiveCoverInfra

set_option linter.unusedSectionVars false

variable (𝕜 : Type w) [Field 𝕜]

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear 𝕜 C]

section Augmentation

variable {P S : C}

/-- For an endomorphism `a : End P`, the scalar `c` such that `a ≫ π = c • π`. -/
def precompScalar (hdim : Module.finrank 𝕜 (P ⟶ S) = 1)
    (π : P ⟶ S) (hπ : π ≠ 0) (a : End P) : 𝕜 :=
  homScalar 𝕜 hdim π hπ (a ≫ π)

end Augmentation
end ProjectiveCoverInfra
end
