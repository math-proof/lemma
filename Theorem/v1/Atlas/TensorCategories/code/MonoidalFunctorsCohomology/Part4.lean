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
import Def.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology.Part4
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


section MonoidalFunctorComposition

/-- Composition of monoidal functor data: composing the underlying group homomorphisms
together with `compCochain2` yields monoidal functor data for the composite. -/
theorem isMonoidalFunctorData_comp {G₁ G₂ G₃ : Type u} [Group G₁] [Group G₂] [Group G₃]
    {A : Type v} [CommGroup A]
    {ω₁ : Cochain3' G₁ A} {ω₂ : Cochain3' G₂ A} {ω₃ : Cochain3' G₃ A}
    {f₁ : G₁ →* G₂} {f₂ : G₂ →* G₃} {μ₁ : Cochain2 G₁ A} {μ₂ : Cochain2 G₂ A}
    (h₁ : IsMonoidalFunctorData G₁ G₂ A ω₁ ω₂ f₁ μ₁)
    (h₂ : IsMonoidalFunctorData G₂ G₃ A ω₂ ω₃ f₂ μ₂) :
    IsMonoidalFunctorData G₁ G₃ A ω₁ ω₃ (f₂.comp f₁) (compCochain2 f₁ μ₁ μ₂) := by
  intro g h l
  unfold IsMonoidalFunctorData at *
  simp only [compCochain2, MonoidHom.comp_apply] at *
  have eq₁ := h₁ g h l
  have eq₂ := h₂ (f₁ g) (f₁ h) (f₁ l)
  rw [← map_mul f₁ h l, ← map_mul f₁ g h] at eq₂
  calc ω₁ g h l * (μ₂ (f₁ h) (f₁ l) * μ₁ h l) * (μ₂ (f₁ g) (f₁ (h * l)) * μ₁ g (h * l))
      = (ω₁ g h l * μ₁ h l * μ₁ g (h * l)) *
        (μ₂ (f₁ h) (f₁ l) * μ₂ (f₁ g) (f₁ (h * l))) := by
          simp [mul_assoc, mul_comm, mul_left_comm]
    _ = (ω₂ (f₁ g) (f₁ h) (f₁ l) * μ₁ g h * μ₁ (g * h) l) *
        (μ₂ (f₁ h) (f₁ l) * μ₂ (f₁ g) (f₁ (h * l))) := by rw [eq₁]
    _ = (ω₂ (f₁ g) (f₁ h) (f₁ l) * μ₂ (f₁ h) (f₁ l) * μ₂ (f₁ g) (f₁ (h * l))) *
        (μ₁ g h * μ₁ (g * h) l) := by
          simp [mul_assoc, mul_comm, mul_left_comm]
    _ = (ω₃ (f₂ (f₁ g)) (f₂ (f₁ h)) (f₂ (f₁ l)) * μ₂ (f₁ g) (f₁ h) * μ₂ (f₁ (g * h)) (f₁ l)) *
        (μ₁ g h * μ₁ (g * h) l) := by rw [eq₂]
    _ = ω₃ (f₂ (f₁ g)) (f₂ (f₁ h)) (f₂ (f₁ l)) *
        (μ₂ (f₁ g) (f₁ h) * μ₁ g h) * (μ₂ (f₁ (g * h)) (f₁ l) * μ₁ (g * h) l) := by
          simp [mul_assoc, mul_comm, mul_left_comm]

end MonoidalFunctorComposition
