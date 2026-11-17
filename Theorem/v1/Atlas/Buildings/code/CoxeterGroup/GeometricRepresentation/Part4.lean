/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Basic.Part3
public import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation
public import Def.v1.Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation.Part3
open Finset BigOperators

public section

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The empty word acts as the identity. -/
@[simp]
theorem wordSigma_nil (M : CoxeterMatrix B) (v : B → ℝ) :
    wordSigma M [] v = v := rfl

/-- A length-one word acts via a single reflection. -/
@[simp]
theorem wordSigma_singleton (M : CoxeterMatrix B) (s : B) (v : B → ℝ) :
    wordSigma M [s] v = sigma M s v := rfl

/-- Cons unfolding: $(s :: w) \cdot v = \sigma_s (w \cdot v)$. -/
@[simp]
theorem wordSigma_cons (M : CoxeterMatrix B) (s : B) (rest : List B) (v : B → ℝ) :
    wordSigma M (s :: rest) v = sigma M s (wordSigma M rest v) := rfl

/-- Concatenation respects composition: $(w_1 \!+\!\!+\, w_2) \cdot v = w_1 \cdot (w_2 \cdot v)$. -/
theorem wordSigma_append (M : CoxeterMatrix B) (w₁ w₂ : List B) (v : B → ℝ) :
    wordSigma M (w₁ ++ w₂) v = wordSigma M w₁ (wordSigma M w₂ v) := by
  induction w₁ with
  | nil => simp
  | cons s rest ih => simp [ih]

/-- Additivity of the word action on vectors. -/
theorem wordSigma_add (M : CoxeterMatrix B) (word : List B) (v₁ v₂ : B → ℝ) :
    wordSigma M word (v₁ + v₂) = wordSigma M word v₁ + wordSigma M word v₂ := by
  induction word with
  | nil => simp [wordSigma]
  | cons s rest ih =>
    simp only [wordSigma]
    rw [ih, sigma_add]

/-- Homogeneity of the word action with respect to scalar multiplication. -/
theorem wordSigma_smul (M : CoxeterMatrix B) (word : List B) (c : ℝ) (v : B → ℝ) :
    wordSigma M word (c • v) = c • wordSigma M word v := by
  induction word with
  | nil => simp [wordSigma]
  | cons s rest ih =>
    simp only [wordSigma]
    rw [ih, sigma_smul]

/-- Every word acts by isometries of $B_M$:
$B_M(\sigma_w v, \sigma_w w') = B_M(v, w')$. -/
theorem wordSigma_preserves_form (M : CoxeterMatrix B) (word : List B) (v w : B → ℝ) :
    bilinForm M (wordSigma M word v) (wordSigma M word w) = bilinForm M v w := by
  have add_right (v w₁ w₂ : B → ℝ) :
      bilinForm M v (w₁ + w₂) = bilinForm M v w₁ + bilinForm M v w₂ := by
    simp only [bilinForm, Pi.add_apply, mul_add]
    simp_rw [Finset.sum_add_distrib]
  have smul_right (v : B → ℝ) (c : ℝ) (w : B → ℝ) :
      bilinForm M v (c • w) = c * bilinForm M v w := by
    simp only [bilinForm, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro _ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro _ _
    ring
  have hsymm (v w : B → ℝ) : bilinForm M v w = bilinForm M w v := by
    simp only [bilinForm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro _ _
    apply Finset.sum_congr rfl
    intro _ _
    rw [formVal_symm]
    ring
  have sigma_as_sum (s : B) (u : B → ℝ) :
      sigma M s u = u + (-2 * bilinForm M u (e s)) • e s := by
    ext t
    simp only [sigma, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have sigma_preserves_form (s : B) (v w : B → ℝ) :
      bilinForm M (sigma M s v) (sigma M s w) = bilinForm M v w := by
    rw [sigma_as_sum s v, sigma_as_sum s w]
    rw [bilinForm_add_left, add_right, add_right]
    rw [bilinForm_smul_left, smul_right]
    rw [bilinForm_smul_left, smul_right]
    rw [bilinForm_e_e, formVal_diag, hsymm (e s) w]
    ring
  induction word with
  | nil => simp
  | cons s rest ih => simp [sigma_preserves_form, ih]


/-- Action on a different basis vector: $\sigma_s(\alpha_t) = \alpha_t - 2\,B_M(\alpha_t,\alpha_s)\,\alpha_s$. -/
theorem sigma_e_other (M : CoxeterMatrix B) (s t : B) :
    sigma M s (e t) = fun u => e t u - 2 * formVal M t s * e s u := by
  ext u
  simp only [sigma, bilinForm_e_e]

end CoxeterGroup
