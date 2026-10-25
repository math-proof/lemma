/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctorProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u v₁ u₁ w


namespace CategoryTheory

/-- `Q` is a retract of `Y` in `C` when there exist morphisms `i : Q ⟶ Y` and
`r : Y ⟶ Q` with `i ≫ r = 𝟙 Q`. -/
def IsRetractOf {C : Type u} [Category.{v} C] (Q Y : C) : Prop :=
  ∃ (i : Q ⟶ Y) (r : Y ⟶ Q), i ≫ r = 𝟙 Q

end CategoryTheory
