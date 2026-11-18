module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorCategoryDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Def.v1.Atlas.TensorCategories.code.TensorExact.Part3
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Def.v1.Atlas.TensorCategories.code.TensorCategoryDef
public section
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits

universe v u

namespace TensorCategories

/-- Definition 1.12.1: a `k`-linear abelian category is locally finite if all hom-spaces are
finite-dimensional over `k` and every object has finite length. -/
class LocallyFiniteCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C] : Prop where
  homFinite : ∀ (X Y : C), Module.Finite k (X ⟶ Y)
  hasFiniteLength : ∀ (X : C), HasFiniteLength X

end TensorCategories
