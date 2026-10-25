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
import Theorem.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology.Part4
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


section MonoidalFunctorComposition

/-- Bundled data of a monoidal functor from `(G₁, ω₁)` to `(G₂, ω₂)`: a group
homomorphism `f`, a 2-cochain `μ`, and the monoidal compatibility condition. -/
structure MonoidalFunctorCocycleData (G₁ G₂ : Type u) [Group G₁] [Group G₂]
    (A : Type v) [CommGroup A] (ω₁ : Cochain3' G₁ A) (ω₂ : Cochain3' G₂ A) where
  f : G₁ →* G₂
  μ : Cochain2 G₁ A
  isMonoidal : IsMonoidalFunctorData G₁ G₂ A ω₁ ω₂ f μ

end MonoidalFunctorComposition
