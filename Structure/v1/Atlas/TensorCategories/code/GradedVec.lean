/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GradedVec.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.GradedObject
import Mathlib.Tactic.Group
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


/-- A 3-cocycle on a monoid `G` with values in a commutative monoid `A`:
a function `ω : G × G × G → A` satisfying the cocycle identity used to
twist the associator of the pointed monoidal category `Vec_G^ω`. -/
structure GroupCocycle3 (G : Type u) [Monoid G] (A : Type v) [CommMonoid A] where
  toFun : G → G → G → A
  cocycle_cond : ∀ g₁ g₂ g₃ g₄ : G,
    toFun (g₁ * g₂) g₃ g₄ * toFun g₁ g₂ (g₃ * g₄) =
    toFun g₁ g₂ g₃ * toFun g₁ (g₂ * g₃) g₄ * toFun g₂ g₃ g₄

