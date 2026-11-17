module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TraceNonzero.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Theorem.v1.Atlas.TensorCategories.code.SimpleObjectHelpers
public section

set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory MonoidalCategory Category

universe w v u


noncomputable section

namespace TensorCategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

variable (k : Type w) [Field k] [IsAlgClosed k]

variable [Preadditive C] [Linear k C] [Abelian C]

variable [MonoidalPreadditive C] [MonoidalLinear k C]

/-- Working semisimplicity assumption on a category: every mono is a split mono and
every epi is a split epi. -/
class SemisimpleCategory (C : Type*) [Category C] : Prop where
  mono_isSplitMono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], IsSplitMono f
  epi_isSplitEpi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], IsSplitEpi f

end TensorCategories
end
