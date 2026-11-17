/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Structure.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part3
@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

universe v u v₁ u₁ w


open TensorCategories in
/-- Reference abbreviation for Definition 1.14.1: a quasi-tensor functor. -/
abbrev Definition_1_14_1_QuasiTensorFunctor := @QuasiTensorFunctor

open TensorCategories in
/-- Reference abbreviation for Definition 1.14.1: a tensor functor. -/
abbrev Definition_1_14_1_TensorFunctor := @TensorFunctor

open TensorCategories in
/-- Reference abbreviation for Definition 1.14.1. -/
abbrev Definition_1_14_1 := @QuasiTensorFunctor

open TensorCategories in
/-- Reference abbreviation for Definition 1.19.1: a quasi-fiber functor. -/
abbrev Definition_1_19_1_QuasiFiberFunctor := @QuasiFiberFunctor

open TensorCategories in
/-- Reference abbreviation for Definition 1.19.1: a fiber functor. -/
abbrev Definition_1_19_1_FiberFunctor := @FiberFunctor

open TensorCategories in
/-- Reference abbreviation for Definition 1.19.1. -/
abbrev Definition_1_19_1 := @FiberFunctor

