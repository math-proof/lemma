/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TraceNonzero.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Theorem.v1.Atlas.TensorCategories.code.SimpleObjectHelpers
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
