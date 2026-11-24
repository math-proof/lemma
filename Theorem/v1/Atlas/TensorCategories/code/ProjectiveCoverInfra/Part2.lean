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
public import Def.v1.Atlas.TensorCategories.code.ProjectiveCoverInfra.Part2
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

end Augmentation
end ProjectiveCoverInfra
end
