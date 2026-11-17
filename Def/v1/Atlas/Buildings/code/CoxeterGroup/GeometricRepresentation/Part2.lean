/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation

@[expose] public section

open Finset BigOperators


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- $\sigma_s$ as a linear automorphism of $\mathbb{R}^B$, built from the involution
property. -/
noncomputable def sigmaLinearEquiv (M : CoxeterMatrix B) (s : B) : (B → ℝ) ≃ₗ[ℝ] (B → ℝ) :=
  LinearEquiv.ofInvolutive (sigmaLinearMap M s) (by
    intro v
    have bilinForm_sigma_e : bilinForm M (sigma M s v) (e s) = -(bilinForm M v (e s)) := by
      have sigma_eq : sigma M s v = v + (-2 * bilinForm M v (e s)) • e s := by
        ext t; simp only [sigma, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [sigma_eq, bilinForm_add_left, bilinForm_smul_left, bilinForm_e_e, formVal_diag]
      ring
    change sigma M s (sigma M s v) = v
    ext t
    simp only [sigma]
    rw [bilinForm_sigma_e]
    ring)

end CoxeterGroup
