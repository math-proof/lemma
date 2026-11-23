/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public import Theorem.v1.Atlas.TensorCategories.code.SemisimpleMultitensor

@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v u


noncomputable section

namespace CategoryTheory

section UnitSemisimple

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

section ComponentSubcategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

omit [HasZeroMorphisms C] in
/-- The `(i, j)`-component object `f i ⊗ X ⊗ f j` formed by sandwiching `X` between two
chosen simple summands of the unit. -/
def componentObj {n : ℕ} (f : Fin n → C) (X : C) (i j : Fin n) : C :=
  f i ⊗ X ⊗ f j

omit [HasZeroMorphisms C] in
/-- The family of all `(i, j)`-component objects of `X`, indexed by pairs in `Fin n × Fin n`. -/
def componentFamily {n : ℕ} (f : Fin n → C) (X : C) : Fin n × Fin n → C :=
  fun p => componentObj f X p.1 p.2

/-- The property that an object lies in the `(i, j)`-component subcategory: it is isomorphic
to `f i ⊗ Y ⊗ f j` for some `Y`. -/
def IsInComponentSubcategory {n : ℕ} (f : Fin n → C) (i j : Fin n) :
    ObjectProperty C :=
  fun X => ∃ (Y : C), Nonempty (X ≅ f i ⊗ Y ⊗ f j)

end ComponentSubcategories
end UnitSemisimple
end CategoryTheory
end
