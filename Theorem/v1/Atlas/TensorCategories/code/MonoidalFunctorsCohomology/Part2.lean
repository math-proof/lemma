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
import Def.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology.Part2
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


section Cohomology

variable (G : Type u) [Group G] (A : Type v) [CommGroup A]

/-- Reformulation of the 3-cocycle condition in the form used to define monoidal
associativity: `ω(g₁g₂, g₃, g₄) ω(g₁, g₂, g₃g₄) = ω(g₁, g₂, g₃) ω(g₁, g₂g₃, g₄) ω(g₂, g₃, g₄)`. -/
theorem isCocycle3_iff_cocycleCond (ω : Cochain3' G A) :
    IsCocycle3 G A ω ↔ ∀ g₁ g₂ g₃ g₄ : G,
      ω (g₁ * g₂) g₃ g₄ * ω g₁ g₂ (g₃ * g₄) =
      ω g₁ g₂ g₃ * ω g₁ (g₂ * g₃) g₄ * ω g₂ g₃ g₄ := by
  unfold IsCocycle3 d3
  constructor
  · intro h g₁ g₂ g₃ g₄
    have := prod5_eq_one_iff.mp (h g₁ g₂ g₃ g₄)

    rw [this]
    simp [mul_comm, mul_left_comm]
  · intro h g₁ g₂ g₃ g₄
    rw [prod5_eq_one_iff]
    have := h g₁ g₂ g₃ g₄
    rw [this]
    simp [mul_comm, mul_left_comm]

end Cohomology
