module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SurjectiveFunctor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Def.v1.Atlas.TensorCategories.code.SurjectiveFunctor
public section

set_option maxHeartbeats 800000

open CategoryTheory

universe v v₁ u u₁


/-- A functor is a surjective tensor functor when every object of the target is a subquotient of
some `F.obj X`. -/
class IsSurjectiveTensorFunctor
    {C : Type u} [Category.{v} C]
    {D : Type u₁} [Category.{v₁} D]
    (F : C ⥤ D) : Prop where
  surjective : ∀ (Y : D), ∃ (X : C), IsSubquotientOf Y (F.obj X)

