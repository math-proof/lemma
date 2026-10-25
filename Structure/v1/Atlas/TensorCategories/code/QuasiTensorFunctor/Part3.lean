/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part4
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

universe v u v₁ u₁ w


namespace TensorCategories

/-- An object `P` of an abelian category `C` is a projective generator if it is
projective and detects zero objects (any `X` admitting only the zero map from `P`
must itself be zero). -/
structure IsProjectiveGenerator
    {C : Type u} [Category.{v} C] [Abelian C] (P : C) : Prop where
  proj : Projective P
  generates : ∀ (X : C), (∀ f : P ⟶ X, f = 0) → Limits.IsZero X

/-- Every finite abelian `k`-linear category with enough projectives admits a
projective generator. -/
structure. -/

end TensorCategories
