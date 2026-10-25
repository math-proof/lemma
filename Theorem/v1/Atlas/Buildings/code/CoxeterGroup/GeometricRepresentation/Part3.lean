/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Basic.Part3
import Def.v1.Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation.Part2
open Finset BigOperators


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- Unfolding lemma: `sigmaLinearEquiv` acts as `sigma`. -/
@[simp]
theorem sigmaLinearEquiv_apply (M : CoxeterMatrix B) (s : B) (v : B → ℝ) :
    sigmaLinearEquiv M s v = sigma M s v := rfl


/-- Additivity of $B_M$ in the right argument. -/
theorem bilinForm_add_right (M : CoxeterMatrix B) (v w₁ w₂ : B → ℝ) :
    bilinForm M v (w₁ + w₂) = bilinForm M v w₁ + bilinForm M v w₂ := by
  simp only [bilinForm, Pi.add_apply, mul_add]
  simp_rw [Finset.sum_add_distrib]

/-- $\mathbb{R}$-linearity of $B_M$ in the right argument. -/
theorem bilinForm_smul_right (M : CoxeterMatrix B) (v : B → ℝ) (c : ℝ) (w : B → ℝ) :
    bilinForm M v (c • w) = c * bilinForm M v w := by
  simp only [bilinForm, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro t _
  ring

/-- Symmetry: $B_M(v, w) = B_M(w, v)$. -/
theorem bilinForm_symm (M : CoxeterMatrix B) (v w : B → ℝ) :
    bilinForm M v w = bilinForm M w v := by
  simp only [bilinForm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro t _
  rw [formVal_symm]
  ring

/-- Each geometric reflection preserves the bilinear form:
$B_M(\sigma_s v, \sigma_s w) = B_M(v, w)$. -/
theorem sigma_preserves_form (M : CoxeterMatrix B) (s : B) (v w : B → ℝ) :
    bilinForm M (sigma M s v) (sigma M s w) = bilinForm M v w := by


  have hv := bilinForm_sigma_e M s v
  have hw := bilinForm_sigma_e M s w


  have sigma_as_sum : ∀ u : B → ℝ,
      sigma M s u = u + (-2 * bilinForm M u (e s)) • e s := by
    intro u; ext t
    simp only [sigma, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [sigma_as_sum v, sigma_as_sum w]
  rw [bilinForm_add_left, bilinForm_add_right, bilinForm_add_right]
  rw [bilinForm_smul_left, bilinForm_smul_right]
  rw [bilinForm_smul_left, bilinForm_smul_right]
  rw [bilinForm_e_e, formVal_diag, bilinForm_symm M (e s) w]
  ring


end CoxeterGroup
