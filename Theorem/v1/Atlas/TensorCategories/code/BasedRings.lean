/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
import Lemma.Category.Atlas.v1.TensorCategories.code.GradedVec
import Lemma.Category.Atlas.v1.TensorCategories.code.TannakaReconstruction
import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
import Structure.v1.Atlas.TensorCategories.code.TannakaReconstruction
import Def.v1.Atlas.TensorCategories.code.BasedRings.Part4
open Finset


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- Cohomology of 3-cocycles is reflexive (taking the trivial 2-cochain). -/
theorem cocycleCohomologous_refl {G : Type*} [Group G] {A : Type*} [CommGroup A]
    (ω : NormalizedGroupCocycle3 G A) : CocycleCohomologous ω ω :=
  ⟨fun _ _ => 1, fun _ _ _ => by simp⟩

/-- Cohomology of 3-cocycles is symmetric: invert the 2-cochain witnessing equivalence. -/
theorem cocycleCohomologous_symm {G : Type*} [Group G] {A : Type*} [CommGroup A]
    {ω₁ ω₂ : NormalizedGroupCocycle3 G A}
    (h : CocycleCohomologous ω₁ ω₂) : CocycleCohomologous ω₂ ω₁ := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun g h => (f g h)⁻¹, fun a b c => ?_⟩
  have h1 := hf a b c
  rw [h1, inv_inv, inv_inv]
  suffices hsuff : ∀ (x a1 a2 a3 a4 : A),
      x * (a1 * a2⁻¹ * a3 * a4⁻¹) * (a1⁻¹ * a2 * a3⁻¹ * a4) = x by
    exact (hsuff _ _ _ _ _).symm
  intro x a1 a2 a3 a4
  calc x * (a1 * a2⁻¹ * a3 * a4⁻¹) * (a1⁻¹ * a2 * a3⁻¹ * a4)
      = x * ((a1 * a1⁻¹) * (a2⁻¹ * a2) * (a3 * a3⁻¹) * (a4⁻¹ * a4)) := by
        simp only [mul_comm, mul_left_comm, mul_assoc]
    _ = x := by simp

/-- Cohomology of 3-cocycles is transitive: compose the witnessing 2-cochains by
multiplying pointwise. -/
theorem cocycleCohomologous_trans {G : Type*} [Group G] {A : Type*} [CommGroup A]
    {ω₁ ω₂ ω₃ : NormalizedGroupCocycle3 G A}
    (h₁₂ : CocycleCohomologous ω₁ ω₂) (h₂₃ : CocycleCohomologous ω₂ ω₃) :
    CocycleCohomologous ω₁ ω₃ := by
  obtain ⟨f, hf⟩ := h₁₂
  obtain ⟨g, hg⟩ := h₂₃
  refine ⟨fun x y => f x y * g x y, fun a b c => ?_⟩
  rw [hg a b c, hf a b c]
  simp only [mul_inv_rev]
  simp only [mul_comm, mul_left_comm, mul_assoc]

end FusionRing
