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
import Structure.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


section MonoidalFunctorComposition

/-- The identity monoidal functor on `(G, ω)`. -/
def MonoidalFunctorCocycleData.id (G : Type u) [Group G] (A : Type v) [CommGroup A]
    (ω : Cochain3' G A) : MonoidalFunctorCocycleData G G A ω ω where
  f := MonoidHom.id G
  μ := fun _ _ => 1
  isMonoidal := isMonoidalFunctorData_id G A ω

/-- Composition of monoidal functor cocycle data. -/
def MonoidalFunctorCocycleData.comp {G₁ G₂ G₃ : Type u}
    [Group G₁] [Group G₂] [Group G₃]
    {A : Type v} [CommGroup A]
    {ω₁ : Cochain3' G₁ A} {ω₂ : Cochain3' G₂ A} {ω₃ : Cochain3' G₃ A}
    (D₁ : MonoidalFunctorCocycleData G₁ G₂ A ω₁ ω₂)
    (D₂ : MonoidalFunctorCocycleData G₂ G₃ A ω₂ ω₃) :
    MonoidalFunctorCocycleData G₁ G₃ A ω₁ ω₃ where
  f := D₂.f.comp D₁.f
  μ := compCochain2 D₁.f D₁.μ D₂.μ
  isMonoidal := isMonoidalFunctorData_comp D₁.isMonoidal D₂.isMonoidal

end MonoidalFunctorComposition
