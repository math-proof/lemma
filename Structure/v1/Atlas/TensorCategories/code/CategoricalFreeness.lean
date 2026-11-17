/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CategoricalFreeness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public section

set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u v₁ u₁ w


namespace CategoryTheory

/-- A surjective quasi-tensor functor between abelian monoidal categories: here packaged as
the underlying functor `F : C ⥤ D`. Used as a stand-in for the data of a quasi-tensor
functor along with the surjectivity hypothesis of Definition 1.49.1. -/
structure SurjectiveQuasiTensorFunctor (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (D : Type u₁) [Category.{v₁} D] [MonoidalCategory D] [Abelian D] where
  F : C ⥤ D

/-- A Frobenius-Perron dimension function `fpDim : C → ℝ` on a monoidal category,
normalized so that `fpDim (𝟙_ C) = 1`, taking positive values, multiplicative on tensor
products and invariant under isomorphisms. -/
structure FPdimFunction {C : Type u} [Category.{v} C] [MonoidalCategory C] where
  fpDim : C → ℝ
  fpDim_unit : fpDim (𝟙_ C) = 1
  fpDim_pos : ∀ (X : C), fpDim X > 0
  fpDim_tensor : ∀ (X Y : C), fpDim (X ⊗ Y) = fpDim X * fpDim Y
  fpDim_iso : ∀ (X Y : C), Nonempty (X ≅ Y) → fpDim X = fpDim Y

end CategoryTheory
