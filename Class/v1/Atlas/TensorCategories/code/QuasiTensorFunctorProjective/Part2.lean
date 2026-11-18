module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctorProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
public import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
public import Instance.v1.Atlas.TensorCategories.code.QuasiTensorFunctorProjective
public section
set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u v₁ u₁ w

namespace CategoryTheory

/-- The monoidal category `C` has a nonzero unit object. -/
class HasNonZeroUnit (C : Type u) [Category.{v} C] [MonoidalCategory C] : Prop where
  unit_nonzero : ¬IsZero (𝟙_ C)

end CategoryTheory
