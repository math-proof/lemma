/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Basic.Part3
open Finset BigOperators


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The bilinear form $B_M$ on $\mathbb{R}^B$ is additive in its left argument. -/
theorem bilinForm_add_left (M : CoxeterMatrix B) (v₁ v₂ w : B → ℝ) :
    bilinForm M (v₁ + v₂) w = bilinForm M v₁ w + bilinForm M v₂ w := by
  simp only [bilinForm, Pi.add_apply, add_mul]
  simp_rw [Finset.sum_add_distrib]

/-- The bilinear form $B_M$ is $\mathbb{R}$-linear in its left argument. -/
theorem bilinForm_smul_left (M : CoxeterMatrix B) (c : ℝ) (v w : B → ℝ) :
    bilinForm M (c • v) w = c * bilinForm M v w := by
  simp only [bilinForm, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro t _
  ring

/-- Additivity: $\sigma_s(v_1 + v_2) = \sigma_s v_1 + \sigma_s v_2$. -/
theorem sigma_add (M : CoxeterMatrix B) (s : B) (v₁ v₂ : B → ℝ) :
    sigma M s (v₁ + v₂) = sigma M s v₁ + sigma M s v₂ := by
  ext t
  simp only [sigma, Pi.add_apply, bilinForm_add_left]
  ring

/-- Homogeneity: $\sigma_s(c \cdot v) = c \cdot \sigma_s v$ for $c \in \mathbb{R}$. -/
theorem sigma_smul (M : CoxeterMatrix B) (s : B) (c : ℝ) (v : B → ℝ) :
    sigma M s (c • v) = c • sigma M s v := by
  ext t
  simp only [sigma, Pi.smul_apply, smul_eq_mul, bilinForm_smul_left]
  ring

end CoxeterGroup
