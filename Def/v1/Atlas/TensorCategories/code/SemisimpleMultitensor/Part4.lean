module
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
public import Theorem.Category.Atlas.v1.TensorCategories.code.PivotalSpherical
public import Theorem.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part3
set_option maxHeartbeats 800000
open CategoryTheory MonoidalCategory CategoryTheory.Limits


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe v u


noncomputable section

namespace CategoryTheory

section UnitSemisimple

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

section ComponentSubcategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

/-- Proposition 1.15.5 (2): on the diagonal `j = k`, the tensor product `C_{ij} ⊗ C_{jl}`
lands in `C_{il}`, exhibited via an explicit isomorphism. -/
noncomputable def tensor_component_compatible {n : ℕ} (f : Fin n → C) [HasBiproduct f]
    (hiso : 𝟙_ C ≅ ⨁ f) (hsimp : ∀ i, Simple (f i))
    (X Y : C) (i j l : Fin n) :
    componentObj f X i j ⊗ componentObj f Y j l ≅ componentObj f ((X ⊗ f j) ⊗ Y) i l := by
  unfold componentObj


  exact
    (α_ (f i) (X ⊗ f j) (f j ⊗ (Y ⊗ f l))) ≪≫
    whiskerLeftIso (f i) (
      (α_ (X ⊗ f j) (f j) (Y ⊗ f l)).symm ≪≫
      whiskerRightIso (
        (α_ X (f j) (f j)) ≪≫
        whiskerLeftIso X (component_diagonal_unit_iso f hiso hsimp j)
      ) (Y ⊗ f l) ≪≫
      (α_ (X ⊗ f j) Y (f l)).symm
    )

end ComponentSubcategories
end UnitSemisimple
end CategoryTheory
end
