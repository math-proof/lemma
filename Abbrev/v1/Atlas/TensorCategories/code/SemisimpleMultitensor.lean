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
public import Def.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part2
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

/-- Definition 1.15.4: the component subcategory `C_{ij} = 𝟙_i ⊗ C ⊗ 𝟙_j` realised as a full
subcategory of `C`. -/
abbrev Definition_1_15_4_ComponentSubcategory {n : ℕ} (f : Fin n → C) (i j : Fin n) :=
  (IsInComponentSubcategory f i j).FullSubcategory

end ComponentSubcategories
end UnitSemisimple
end CategoryTheory
end
