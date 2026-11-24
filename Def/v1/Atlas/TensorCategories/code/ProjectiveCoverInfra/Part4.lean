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
public import Theorem.v1.Atlas.TensorCategories.code.ProjectiveCoverInfra.Part3
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
end
