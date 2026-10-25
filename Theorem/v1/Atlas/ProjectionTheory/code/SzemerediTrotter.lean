/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SzemerediTrotter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.SzemerediTrotter
open Finset Real


noncomputable section

namespace ProjectionTheory

/-- The projection map $\pi_\theta : \mathbb{R}^2 \to \mathbb{R}$ is surjective. -/
lemma projR2Lin_surjective (θ : ℝ) : Function.Surjective (projR2Lin θ) := by
  intro y
  refine ⟨![y * Real.cos θ, y * Real.sin θ], ?_⟩
  simp only [projR2Lin, projR2, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have key : y * Real.cos θ * Real.cos θ + y * Real.sin θ * Real.sin θ = y := by
    have : y * Real.cos θ * Real.cos θ + y * Real.sin θ * Real.sin θ
        = y * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
    rw [this, Real.cos_sq_add_sin_sq, mul_one]
  linarith [key]

/-- For $\theta \in [0, \pi)$, the kernel of $\pi_\theta$ is a $1$-dimensional subspace
of $\mathbb{R}^2$, so its fibers are honest lines. -/
lemma projR2Lin_ker_finrank (θ : ℝ) (hθ : 0 ≤ θ ∧ θ < Real.pi) :
    Module.finrank ℝ (LinearMap.ker (projR2Lin θ)) = 1 := by
  have h_rank_ker := (projR2Lin θ).finrank_range_add_finrank_ker
  have h_total : Module.finrank ℝ (Fin 2 → ℝ) = 2 := by simp
  rw [h_total] at h_rank_ker
  suffices h_range : Module.finrank ℝ (LinearMap.range (projR2Lin θ)) = 1 by omega
  have h_surj : LinearMap.range (projR2Lin θ) = ⊤ :=
    LinearMap.range_eq_top.mpr (projR2Lin_surjective θ)
  rw [h_surj]; simp [Module.finrank_self]

end ProjectionTheory
end
