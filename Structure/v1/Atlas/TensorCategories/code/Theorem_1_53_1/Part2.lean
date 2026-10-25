/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_53_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Def.v1.Atlas.TensorCategories.code.Theorem_1_53_1.Part2
set_option maxHeartbeats 400000
set_option autoImplicit false

open CategoryTheory MonoidalCategory

universe u v w


section DimProjZero

open CategoryTheory MonoidalCategory

variable {k : Type w} [Field k]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]


/-- Bundle of data abstracting the relevant features of a finite tensor category with
pivotal structure: simple objects, their projective covers, the Cartan matrix,
and pivotal-dimension data (with the extracted scalar `φ` and required identities). -/
structure FiniteTensorCategoryData (C : Type u)
    [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    (k : Type w) [Field k]
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (u : PivotalStructureData C) where
  simpleObj : ι → C
  unitIndex : ι
  unitIso : Nonempty (simpleObj unitIndex ≅ 𝟙_ C)
  projCover : ι → C
  projCover_projective : ∀ i, Projective (projCover i)
  cartanEntry : ι → ι → ℕ
  φ : (𝟙_ C ⟶ 𝟙_ C) → k
  retract_of_projective : ∀ (Q : C) [Projective Q],
    φ (pivotalDim C u Q) ≠ 0 → Projective (𝟙_ C)
  dim_unit_ne_zero : φ (pivotalDim C u (𝟙_ C)) ≠ 0
  dim_iso_invariant : ∀ (X Y : C), Nonempty (X ≅ Y) →
    pivotalDim C u X = pivotalDim C u Y
  additive_on_composition_series : ∀ i,
    ∑ j : ι, (cartanEntry i j : k) * φ (pivotalDim C u (simpleObj j)) =
      φ (pivotalDim C u (projCover i))


end DimProjZero
