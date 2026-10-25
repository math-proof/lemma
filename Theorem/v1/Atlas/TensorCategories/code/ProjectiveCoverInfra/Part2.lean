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
import Def.v1.Atlas.TensorCategories.code.ProjectiveCoverInfra.Part2
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
