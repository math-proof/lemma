/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.GradedVec
import Mathlib.GroupTheory.GroupAction.Basic
import Theorem.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology.Part3
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


section MonoidalFunctorComposition

/-- Composition of 2-cochains along a group homomorphism `f₁ : G₁ →* G₂`: the
2-cochain `μ₂(f₁ g, f₁ h) * μ₁(g, h)` on `G₁`. -/
def compCochain2 {G₁ G₂ : Type u} [Group G₁] [Group G₂] {A : Type v} [CommGroup A]
    (f₁ : G₁ →* G₂) (μ₁ : Cochain2 G₁ A) (μ₂ : Cochain2 G₂ A) : Cochain2 G₁ A :=
  fun g h => μ₂ (f₁ g) (f₁ h) * μ₁ g h

end MonoidalFunctorComposition
