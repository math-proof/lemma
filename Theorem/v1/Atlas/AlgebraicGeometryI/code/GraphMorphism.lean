/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GraphMorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Instance.v1.Atlas.AlgebraicGeometryI.code.GraphMorphism
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u


namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The graph morphism fits into a pullback square exhibiting `Γ_f` as the pullback of the
diagonal `Δ_Y` along `f × 𝟙_Y : X × Y → Y × Y`. -/
theorem isPullback_graphMor :
    IsPullback f (graphMor f) (prod.lift (𝟙 Y) (𝟙 Y)) (prod.map f (𝟙 Y)) := by
  refine ⟨⟨by ext <;> simp⟩,
    ⟨PullbackCone.IsLimit.mk _ (fun s => s.snd ≫ prod.fst) ?_ ?_ ?_⟩⟩
  ·
    intro s
    have h1 := congr_arg (· ≫ prod.fst) s.condition
    simp [Category.assoc, prod.lift_fst, prod.map_fst] at h1
    exact h1.symm
  ·
    intro s
    have h1 := congr_arg (· ≫ prod.fst) s.condition
    simp [Category.assoc, prod.lift_fst, prod.map_fst] at h1
    have h2 := congr_arg (· ≫ prod.snd) s.condition
    simp [Category.assoc, prod.lift_snd, prod.map_snd] at h2
    apply prod.hom_ext
    · simp [prod.lift_fst]
    · simp [prod.lift_snd, Category.assoc]; rw [← h1, h2]
  ·
    intro s m hfst hsnd
    have := congr_arg (· ≫ prod.fst) hsnd
    simp [prod.lift_fst] at this
    exact this

end AlgebraicGeometry.Scheme
