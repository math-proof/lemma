/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorCategoryDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Def.v1.Atlas.TensorCategories.code.TensorExact.Part3
public import Theorem.Category.Atlas.v1.TensorCategories.code.TensorExact
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.CategoryTheory.Subobject.Lattice
@[expose] public section
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits

universe v u


namespace TensorCategories

/-- An object `X` has finite length if the lattice of its subobjects is both
Noetherian (well-founded `<`) and Artinian (well-founded `>`). -/
def HasFiniteLength {C : Type u} [Category.{v} C] (X : C) : Prop :=
  WellFoundedLT (Subobject X) ∧ WellFoundedGT (Subobject X)

end TensorCategories
